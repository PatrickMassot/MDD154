import tactic

namespace tactic
setup_tactic_parser

meta def nettoyage : tactic unit := 
do try `[dsimp only at * { eta := false, beta := true }],
   try `[simp only [exists_prop] at *]

def force_type (p : Sort*) (x : p) := p

meta def verifie_nom (n : name) :=
success_if_fail (do hyp ← get_local n, skip) <|> 
fail ("Le nom " ++ n.to_string ++ " est déjà utilisé.")

@[derive has_reflect]
inductive intro_rel
| lt | gt | le | ge | mem

@[derive has_reflect]
meta inductive introduced
| typed (n : name) (e : pexpr) : introduced
| bare (n : name) : introduced
| related (n : name) (rel : intro_rel) (e : pexpr) : introduced

-- Les deux fonctions suivantes sont en chantier, le but était de permettre d'utiliser introduced
-- aussi dans on obtient

meta def introduced.related_hyp (n : name) (rel : intro_rel) (pe : pexpr) : pexpr :=
match rel with
| intro_rel.lt  := ```(n < %%pe)
| intro_rel.gt  := ```(n > %%pe)
| intro_rel.le  := ```(n ≤ %%pe)
| intro_rel.ge  := ```(n ≥ %%pe)
| intro_rel.mem := ```(n ∈ %%pe)
end

meta def introduced.related_hyp_name (n : name) (rel : intro_rel) (pe : pexpr) : name :=
if pe = ``(0) then
   match rel with
   | intro_rel.lt  := n.to_string ++ "_neg"
   | intro_rel.gt  := n.to_string ++ "_pos"
   | intro_rel.le  := n.to_string ++ "_neg"
   | intro_rel.ge  := n.to_string ++ "_pos"
   | intro_rel.mem := "h_" ++ n.to_string -- ne devrait pas arriver
   end
else 
   match rel with
   | intro_rel.lt  := n.to_string ++ "_lt"
   | intro_rel.gt  := n.to_string ++ "_gt"
   | intro_rel.le  := n.to_string ++ "_le"
   | intro_rel.ge  := n.to_string ++ "_ge"
   | intro_rel.mem := n.to_string ++ "_mem"
   end

meta def parse_intro_rel : lean.parser intro_rel :=
intro_rel.lt <$ tk "<" <|>
intro_rel.gt <$ tk ">" <|>
intro_rel.le <$ tk "≤" <|>
intro_rel.le <$ tk "<=" <|>
intro_rel.ge <$ tk "≥" <|>
intro_rel.ge <$ tk ">=" <|>
intro_rel.mem <$ tk "∈"

meta def intro_parser : lean.parser introduced :=
do n ← ident,
   (introduced.typed n <$> (tk ":" *> texpr)) <|>
   (introduced.related n <$> parse_intro_rel <*> texpr) <|>
   pure (introduced.bare n)

meta def bracketed_intro_parser : lean.parser introduced :=
with_desc "..." $
(brackets "(" ")" intro_parser) <|> intro_parser

@[derive has_to_format]
meta def maybe_typed_ident := name × option pexpr

meta def maybe_typed_ident_parser : lean.parser maybe_typed_ident :=
do { n ← (tk "(" *> ident), pe ← (tk ":" *> texpr <* tk ")"), return (n, some pe) } <|>
do { n ← ident, 
     do { pe ← (tk ":" *> texpr), pure (n, some pe) } <|> pure (n, none) }

meta def rcases_patt_of_maybe_typed_ident : maybe_typed_ident → rcases_patt
| (n, some pe) := rcases_patt.typed (rcases_patt.one n) pe
| (n, none)    := rcases_patt.one n

meta def rcases_patt_list_of_introduced_list : list introduced → list rcases_patt
| (introduced.typed n pe :: tail) := 
    (rcases_patt.typed (rcases_patt.one n) pe) :: rcases_patt_list_of_introduced_list tail 
| (introduced.related n rel pe :: tail) := []
| (introduced.bare n  :: tail) := 
    (rcases_patt.one n) :: rcases_patt_list_of_introduced_list tail 
|_ := []

meta def mk_mapp_pexpr_aux : expr → expr → list pexpr → tactic expr
| fn (expr.pi n bi d b) (a::as) :=
do a ← to_expr a,
   infer_type a >>= unify d,
   fn ← head_beta (fn a),
   t ← whnf (b.instantiate_var a),
   mk_mapp_pexpr_aux fn t as
| fn _ [] := pure fn
| fn _ _ := fail "Il y a trop d'arguments"

/-- Applique une expression à une liste de pré-expressions. -/
meta def mk_mapp_pexpr (fn : expr) (args : list pexpr) : tactic expr :=
do t ← infer_type fn >>= whnf,
   mk_mapp_pexpr_aux fn t args

/-- Applique une pré-expression à une liste de pré-expressions. -/
meta def pexpr_mk_app : pexpr → list pexpr → pexpr
| e []      := e
| e (x::xs) := pexpr_mk_app (e x) xs

/-- Parse une liste d'arguments, peut-être vide. -/
meta def applique_a_parser : lean.parser (list pexpr) :=
(tk "appliqué" *> tk "à" *> pexpr_list_or_texpr) <|> pure []

meta def apply_arrow_to_hyp (e : pexpr) (hyp : expr) : tactic unit :=
do {
  t ← infer_type hyp,
  e_expr ← to_expr e,
  e_type ← infer_type e_expr,
  e_is_prop ← is_prop e_type,
  if e_is_prop then do
    prf ← interactive.mk_mapp' e_expr [hyp],
    clear hyp,
    hyp ← note hyp.local_pp_name none prf,
    nettoyage
  else do
    prf ← match t with
    | `(%%l = %%r) := do
          ltp ← infer_type l,
          mv ← mk_mvar,
          to_expr ``(congr_arg (%%e : %%ltp → %%mv) %%hyp)
    | _ := fail ("failed to apply " ++ to_string e ++ " at " ++ to_string hyp.local_pp_name)
    end,
    clear hyp,
    hyp ← note hyp.local_pp_name none prf,
    nettoyage
}

@[interactive]
meta def apply_arrow (q : parse texpr) (locs : parse location) 
  : tactic unit :=
match locs with
| (loc.ns l) := l.mmap' $ option.mmap $ λ h, get_local h >>= apply_arrow_to_hyp q
| wildcard   := local_context >>= list.mmap' (apply_arrow_to_hyp q)
end

example (P Q R : Prop) (h : P → Q) (h' : P) : Q :=
begin
  apply_arrow h at h',
  exact h',
end

example (f : ℕ → ℕ) (a b : ℕ) (h : a = b) : f a = f b :=
begin
  apply_arrow f at h,
  exact h
end
/-- Si `e` est une conjonction, on la sépare et on renvoit la liste des deux membres, 
    sinon on renvoit la liste [e] -/
meta def split_and (e : expr) : tactic (list expr) :=
do e_type ← infer_type e >>= whnf,
   match e_type with
   | `(%%P ∧ %%Q) := do l ← tactic.cases_core e,
                        pure (l.map (λ x : name × list expr × list (name × expr), x.2.1)).join
   | _ := pure [e]
   end

/- Sépare toutes les conjonctions dans la liste d'expressions -/
meta def split_ands (hyps : list expr) : tactic (list pexpr) :=
do l ← hyps.mmap (λ e : expr, if e.is_local_constant then split_and e else pure [e]),
   pure (l.join.map to_pexpr)

meta def conclure (pe : pexpr) (args : list pexpr) : tactic unit :=
focus1 (do
  let pprf := pexpr_mk_app pe args,
  tgt ← target,
  (i_to_expr_strict ``(%%pprf : %%tgt) >>= exact) <|>
  linarith ff tt [pprf] <|> 
  do { proof ← to_expr pprf, 
       split_ands [proof] >>= linarith ff tt <|> 
       apply proof >> done } <|>
  fail "Cela ne conclut pas")
end tactic