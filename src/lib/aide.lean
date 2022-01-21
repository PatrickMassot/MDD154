import tactic.linarith
import lib.interactive_expr


meta def rel_symb : expr → tactic (expr × expr × string)
| `(%%x < %%y) := pure (x, y, " < ")
| `(%%x ≤ %%y) := pure (x, y, " ≤ ")
| `(%%x > %%y) := pure (x, y, " > ")
| `(%%x ≥ %%y) := pure (x, y, " ≥ ")
| `(%%x ∈ %%y) := pure (x, y, " ∈ ")
| e := do pe ← tactic.pp e, tactic.fail $ "Not a relation: " ++ pe.to_string

section
open expr

/-- Une version de `expr.rename_var` qui renomme même les variables libres. -/
meta def expr.rename (old new : name) : expr → expr
| (pi n bi t b) := (pi (if n = old then new else n) bi (expr.rename t) (expr.rename b))
| (lam n bi t b) := (lam (if n = old then new else n) bi (expr.rename t) (expr.rename b))
| (app t b) := (app (expr.rename t) (expr.rename b))
| (local_const n nn bi t) := (local_const (if n = old then new else n) (if nn = old then new else nn) bi $ expr.rename t)
| e := e

end

/-- Mini language d'expression où les quantificateurs bornés et les connecteurs ∧, ∨ et ↔ sont des citoyens à part entière. -/
meta inductive my_expr
| forall_rel (var_name : name) (typ : expr) (rel : string) (rel_rhs : expr) (propo : my_expr) : my_expr
| forall_simple (var_name : name) (typ : expr) (propo : my_expr) : my_expr
| exist_rel (var_name : name) (typ : expr) (rel : string) (rel_rhs : expr) (propo : my_expr) : my_expr
| exist_simple (var_name : name) (typ : expr) (propo : my_expr) : my_expr
| conjunction (propo propo' : my_expr) : my_expr
| disjunction (propo propo' : my_expr) : my_expr
| impl (le re : expr) (lhs : my_expr) (rhs : my_expr) : my_expr
| ssi (le re : expr) (lhs rhs : my_expr) : my_expr
| egal (le re : expr) : my_expr
| ineq (le : expr) (symb : string) (re : expr) : my_expr
| prop (e : expr) : my_expr
| data (e : expr) : my_expr

namespace my_expr

meta def tofmt : my_expr →  tactic format 
| (forall_rel var_name typ rel rel_rhs propo) := do
    rhs ← tactic.pp rel_rhs,
    p ← tofmt propo,
    pure $ "∀ " ++ var_name.to_string ++ rel ++ rhs.to_string ++ ", " ++ p
| (forall_simple var_name typ propo) := do
    p ← tofmt propo,
    pure $ "∀ " ++ var_name.to_string ++ ", " ++ p
| (exist_rel var_name typ rel rel_rhs propo) := do
    rhs ← tactic.pp rel_rhs,
    p ← tofmt propo,
    pure $ "∃ " ++ var_name.to_string ++ rel ++ rhs.to_string ++ ", " ++ p
| (exist_simple var_name typ propo) := do
    p ← tofmt propo,
    pure $ "∃ " ++ var_name.to_string ++ ", " ++ p
| (conjunction propo propo') := do
    p ← tofmt propo,
    p' ← tofmt propo',
    pure $ p ++ " ∧ " ++ p'
| (disjunction propo propo') := do
    p ← tofmt propo,
    p' ← tofmt propo',
    pure $ p ++ " ∨ " ++ p'
| (impl le re lhs rhs) := do 
  l ← tofmt lhs,
  r ← tofmt rhs,
  pure $ l ++ " → " ++ r
| (ssi le re lhs rhs) := do 
  l ← tofmt lhs,
  r ← tofmt rhs,
  pure $ l ++ " ↔ " ++ r
| (egal le re) := do 
  l ← tactic.pp le,
  r ← tactic.pp re,
  pure $ l ++ " = " ++ r
| (ineq le symb re) := do 
  l ← tactic.pp le,
  r ← tactic.pp re,
  pure $ l ++ symb ++ r
| (prop e) := tactic.pp e
| (data e) := tactic.pp e

meta instance : has_to_tactic_format my_expr :=
⟨my_expr.tofmt⟩

/-- Définitions à tenter de déplier quand on ne reconnait ni un ∀ ni un ∃. -/
def unfold_defs : list name := [`borne_sup, `continue_en, `croissante, `decroissante, 
  `est_borne_inf, `est_borne_sup, `extraction, `impair, `impaire, `injective, 
  `limite_infinie_suite, `limite_infini_suite, `limite_moins_infini_suite,
  `limite_suite, `majorant, `majoree, `minorant, `minoree, `pair, `paire, `pgcd,
  `segment, `suite_cauchy, `suite_croissante, `suite_decroissante, `surjective,
  `valeur_adherence]

meta def parse : expr → tactic my_expr
| e@(expr.pi n bi t b) := do
    var ← tactic.mk_local' n bi t,
    match (expr.instantiate_var b var) with
    | e'@(expr.pi n' bi' t' b') := 
      do { (x, y, symbole) ← rel_symb t',
           --tactic.trace (rel_symb t'),
           when (x.local_pp_name ≠ n) $ tactic.fail "",
/-            tactic.trace "e : ", tactic.trace e,
           tactic.trace "e' : ", tactic.trace e',
           tactic.trace "n : ", tactic.trace n,
           tactic.trace "n' :", tactic.trace n',
           tactic.trace "t' :", tactic.trace t',
           tactic.trace y,
 -/           var' ← tactic.mk_local' n' bi' t',
           my_expr.forall_rel n t symbole y <$> parse (expr.instantiate_var b' var') } <|>
      do { typ ← parse t,
           body ← parse e',
           if e.is_arrow then 
              pure (impl t e' typ body) 
           else 
             pure $ my_expr.forall_simple n t body }
    | e' := do 
           typ ← parse t,
           body ← parse e',
            if e.is_arrow then 
              pure (impl t e' typ body) 
            else 
              forall_simple n t <$> parse (expr.instantiate_var b var)
    end
|`(@Exists %%α %%p) := 
  do {
    `(@Exists %%α' %%p') ← pure p.binding_body,
    var ← tactic.mk_local' p.binding_name p.binding_info p.binding_domain,
    (x, y, symbole) ← rel_symb α'.binding_body, 
    exist_rel p.binding_name α symbole y <$> parse (expr.instantiate_var p' var).binding_body } <|> 
  do { 
    var ← tactic.mk_local' p.binding_name p.binding_info p.binding_domain,
    exist_simple p.binding_name α <$> parse (expr.instantiate_var p.binding_body var)
    }
|`(and %%e %%e') := do 
    p ← parse e,
    p' ← parse e',
    pure $ conjunction p p'
|`(or %%e %%e') := do 
    p ← parse e,
    p' ← parse e',
    pure $ disjunction p p'
|`(iff %%e %%e') := do 
    p ← parse e,
    p' ← parse e',
    pure $ ssi e e' p p'
|`(eq %%e %%e') := pure $ egal e e'
| `(%%x < %%y) := pure $ ineq x " < " y
| `(%%x ≤ %%y) := pure $ ineq x " ≤ " y
| `(%%x > %%y) := pure $ ineq x " > " y
| `(%%x ≥ %%y) := pure $ ineq x " ≥ " y
| e := do { e' ← tactic.delta unfold_defs e,
            tactic.trace  "Remarque : La commande",
            tactic.trace  " On déplie nom,",
            tactic.trace  "ou",
            tactic.trace  " On déplie nom dans hyp,",
            tactic.trace  "permet de déplier la définition nom dans le but ou dans une hypothèse hyp.",
            tactic.trace  "",
            parse e' } <|> 
       do { t ← tactic.infer_type e, pure $ if t = `(Prop) then prop e else data e } <|> pure (prop e)

meta def rename (old new : name) : my_expr → my_expr
| (forall_rel n typ rel rel_rhs propo) := forall_rel (if n = old then new else n) typ rel rel_rhs $ rename propo
| (forall_simple n typ propo) := forall_simple (if n = old then new else n) typ $ rename propo
| (exist_rel n typ rel rel_rhs propo) := exist_rel (if n = old then new else n) typ rel rel_rhs $ rename propo
| (exist_simple n typ propo) := exist_simple (if n = old then new else n) typ $ rename propo
| (conjunction propo propo') := conjunction (rename propo) (rename propo')
| (disjunction propo propo') := disjunction (rename propo) (rename propo')
| (impl le re lhs rhs) := impl (le.rename_var old new) (re.rename_var old new) (rename lhs) (rename rhs)
| (ssi le re lhs rhs) := ssi (le.rename_var old new) (re.rename_var old new) (rename lhs) (rename rhs)
| (egal le re) := egal (le.rename_var old new) (re.rename_var old new)
| (ineq le rel re) := ineq (le.rename_var old new) rel (re.rename_var old new)
| (prop e) := prop (e.rename old new)
| (data e) := data (e.rename old new)


/- meta def P : expr := expr.local_const `P `P binder_info.default `(ℕ → Prop)
meta def n : expr := expr.local_const `n `n binder_info.default `(ℕ)
meta def m : expr := expr.app P n

run_cmd tactic.pp (expr.rename `n `k m) >>= tactic.trace 

run_cmd tactic.pp ((my_expr.prop m).rename `n `k) >>= tactic.trace 
 -/

end my_expr

namespace tactic.interactive
setup_tactic_parser
open tactic my_expr

meta def test (h : parse ident) : tactic unit :=
do t ← get_local h >>= infer_type,
   trace t,
   parse t >>= trace

end tactic.interactive

/- section tests
example (Q R : ℕ → Prop) (P : ℕ → ℕ → Prop) 
  (h₁ : R 1 → Q 2) 
  (h₂ : ∀ k ≥ 2, ∃ n ≥ 3, ∀ l, l - n = 0 → P l k) 
  (h₃ : ∃ n ≥ 5, Q n)
  (h₄ : ∀ k ≥ 2, ∃ n ≥ 3, P n k)
  (h₅ : ∃ n, Q n)
  (h₆ : ∀ k, ∃ n, P n k)
  (h₇ : ∀ k ≥ 2, ∃ n, P n k) 
  (h₈ : (∀ k : ℕ, Q k) → (∀ l , R l))
  (h₉ : (∀ k : ℕ, Q k) ↔ (∀ l , R l))
  (h₁₀ : ∀ k, 1 ≤ k → Q k)
  (h₁₁ : ∀ k, ∀ l, k ≤ l → P k l) : true :=
begin
  test h₁,
  test h₂,
  test h₃,
  test h₄,
  test h₅,
  test h₆,
  test h₇,
  test h₈,
  test h₉,
  test h₁₀,
  test h₁₁,
  trivial
end

end tests -/

meta def symb_to_hyp : string → expr → string
| " ≥ " `(0) := "_pos"
| " ≥ " _ := "_sup"  
| " > " `(0) := "_pos"
| " > " _ := "_sup"  
| " ≤ " `(0) := "_neg"
| " ≤ " _ := "_inf"  
| " < " `(0) := "_neg"
| " < " _ := "_inf"  
| " ∈ " _ := "_dans"
| _ _ := ""

meta def describe : string → string
| "ℝ" := "un nombre réel"
| "ℕ" := "un nombre entier naturel"
| "ℤ" := "un nombre entier relatif"
| t := "une expression de type " ++ t

meta def describe_pl : string → string
| "ℝ" := "des nombres réels"
| "ℕ" := "des nombres entiers naturels"
| "ℤ" := "des nombres entiers relatifs"
| t := "des expressions de type " ++ t

def libre (s: string) : string := "Le nom " ++ s ++ " peut être choisi librement parmi les noms disponibles."

def libres (ls : list string) : string :=
"Les noms " ++ string.intercalate ", " ls ++ " peuvent être choisis librement parmi les noms disponibles."

meta def applique_a : list format → string
| [] := ""
| [x] := " appliqué à " ++ x.to_string
| s@(x::t) := " appliqué à " ++ s.to_string

section
open tactic my_expr

meta def tactic.aide : option name → tactic unit 
| (some h) := do
  let sh := h.to_string,
  eh ← get_local h <|> fail ("Il n'y a pas d'hypothèse appellée " ++ sh),
  hyp ← infer_type eh,
  but ← to_string <$> (target >>= pp),
  msg ← lock_tactic_state $ do { 
    r ← tactic.apply_core eh {}, -- On essaie d'appliquer `h`
    l ← r.mmap (λ p : name × expr, tactic.instantiate_mvars p.2),  -- on instancie les méta-variables qui peuvent l'être
    l' ← (l.filter (λ v : expr, not v.is_mvar)).mmap pp, -- on regarde ce qui a réussit à être unifié à la ligne du dessus
    do { ptgt ← to_string <$> (target >>= pp), -- Cette ligne va échouer s'il ne reste plus de but après `apply`
         pure $ "  Par " ++ sh ++ applique_a l' ++ " il suffit de montrer que " ++ ptgt ++ 
         ",\n\nSi vous disposez déjà d'une démonstration H de " ++ ptgt ++  
         " alors on peut utiliser :\n  On conclut par " ++ sh ++ applique_a (l' ++ ["H"]) ++ "," } <|>
    do { pure $ "  On conclut par " ++ sh ++ applique_a l' ++ "," } 
    } <|> pure "",
  m ← parse hyp,
  match m with
  | (forall_rel var_name typ rel rel_rhs propo) := do
      py ← pp rel_rhs,
      t ← pp typ,
      
      let n := var_name.to_string,
      let n₀ := n ++ "₀",
      let nn₀ := mk_simple_name n₀,
      p ← to_string <$> pp (propo.rename var_name nn₀),
      match propo with
      | (exist_rel var_name' typ' rel' rel_rhs' propo') := do 
        let n' := var_name'.to_string,
        py' ← to_string <$> pp rel_rhs',
        p' ← to_string <$> pp (propo'.rename var_name nn₀),
        trace $ "L'hypothèse " ++ sh ++ " commence par « ∀ " ++ n ++ rel ++ py.to_string ++ ", ∃ " ++ n' ++ rel' ++ py' ++ ", ... »",
        trace "On peut l'utiliser avec :",
        trace ("  Par " ++ sh ++ " appliqué à [" ++ n₀ ++ ", h" ++ n₀ ++ "] on obtient " ++ n' ++ " tel que (" ++
          n' ++ symb_to_hyp rel' rel_rhs' ++ " : " ++ n' ++ rel' ++ py' ++ ") (h" ++ n' ++ ": " ++ p' ++ "),"),
        trace ("où " ++ n₀ ++ " est " ++ describe t.to_string ++ 
               " et h" ++ n₀ ++ " est une démonstration du fait que " ++ n₀ ++ rel ++ py.to_string),
        trace $ libres [n' ++ symb_to_hyp rel' rel_rhs', "h" ++ n']
      | (exist_simple var_name' typ' propo') := do
        let n' := var_name'.to_string,
        p' ← to_string <$> pp (propo'.rename var_name nn₀),
        trace $ "L'hypothèse " ++ sh ++ " commence par « ∀ " ++ n ++ rel ++ py.to_string ++ ", ∃ " ++ n'  ++ ", ... »",
        trace "On peut l'utiliser avec :",
        trace ("  Par " ++ sh ++ " appliqué à [" ++ n₀ ++ ", h" ++ n₀ ++"] on obtient " ++ n' ++ " tel que (h" ++ n' ++ ": " ++ p' ++ "),"),
        trace ("où " ++ n₀ ++ " est " ++ describe t.to_string ++ 
               " et h" ++ n₀ ++ " est une démonstration du fait que " ++ n₀ ++ rel ++ py.to_string),
        trace $ libres [n', "h" ++ n']
      | _ := do 
        trace $ "L'hypothèse " ++ sh ++ " commence par « ∀ " ++ var_name.to_string ++ rel ++ py.to_string ++ ", »",
        trace "On peut l'utiliser avec :",
        trace ("  Par " ++ sh ++ " appliqué à " ++ n₀ ++ " on obtient (h : " ++ p ++ "),"),
        trace $ "où " ++ n₀ ++ " est " ++ describe t.to_string,
        trace $ libre "h"
      end
  | (forall_simple var_name typ propo) := do
      t ← pp typ,
      let n := var_name.to_string,
      let n₀ := n ++ "₀",
      let nn₀ := mk_simple_name n₀,
      p ← to_string <$> pp (propo.rename (mk_simple_name n) nn₀),
      match propo with
      | (exist_rel var_name' typ' rel' rel_rhs' propo') := do 
        let n' := var_name'.to_string,
        py' ← to_string <$> pp rel_rhs',
        p' ← to_string <$> pp (propo'.rename var_name nn₀),
        trace $ "L'hypothèse " ++ sh ++ " commence par « ∀ " ++ n ++ "," ++ "∃ " ++ n' ++ rel' ++ py' ++ ", ... »",
        trace "On peut l'utiliser avec :",
        trace ("  Par " ++ sh ++ " appliqué à " ++ n₀ ++ " on obtient " ++ n' ++ " tel que (" ++
          n' ++ symb_to_hyp rel' rel_rhs' ++ " : " ++ n' ++ rel' ++ py' ++ ") (h" ++ n' ++ ": " ++ p' ++ "),"),
        trace $ "où " ++ n₀ ++ " est " ++ describe t.to_string,
        trace $ libres [n', n' ++ symb_to_hyp rel' rel_rhs', "h" ++ n']
      | (exist_simple var_name' typ' propo') := do
        let n' := var_name'.to_string,
        p' ← to_string <$> pp (propo'.rename var_name nn₀),
        trace $ "L'hypothèse " ++ sh ++ " commence par « ∀ " ++ n ++ ", ∃ " ++ n'  ++ ", ... »",
        trace "On peut l'utiliser avec :",
        trace ("  Par " ++ sh ++ " appliqué à " ++ n₀ ++" on obtient " ++ n' ++ " tel que (h" ++ n' ++ ": " ++ p' ++ "),"),
        trace $ "où " ++ n₀ ++ " est " ++ describe t.to_string,
        trace $ libres [n', "h" ++ n']
      | (forall_rel var_name' typ' rel' rel_rhs' propo') := do
        let n' := var_name'.to_string,
        py' ← to_string <$> pp rel_rhs',
        p' ← to_string <$> pp (propo'.rename var_name nn₀),
        let rel := n ++ rel' ++ n',
        trace $ "L'hypothèse " ++ sh ++ " commence par « ∀ " ++ n ++ " " ++ n' ++", " ++ rel ++ " → ... ",
        trace "On peut l'utiliser avec :",
        trace ("  Par " ++ sh ++ " appliqué à ["++n++", "++n'++", H] on obtient (h : " ++ p' ++ "),"),
        trace $ "où " ++ n ++ " et " ++ n' ++ " sont " ++ describe_pl t.to_string ++ " et H est une démonstration de " ++ rel,
        trace $ libre "h"
      | _ := do 
        trace $ "L'hypothèse " ++ sh ++ " commence par « ∀ " ++ n ++ ", »",
        trace "On peut l'utiliser avec :",
        trace $ "  Par " ++ sh ++ " appliqué à " ++ n₀ ++ " on obtient (h : " ++ p ++ "),",
        trace $ "où " ++ n₀ ++ " est " ++ describe t.to_string,
        trace $ libre "h",
        trace $ "\nSi cette hypothèse ne servira plus dans sa forme générale, on peut aussi spécialiser " ++ sh ++ " par",
        trace $ "  On applique " ++ sh ++ " à " ++ n₀ ++ ",",
        when (msg ≠ "") (do 
          trace $ "\nComme le but est " ++ but ++ ", on peut utiliser :",
          trace $ msg)
      end
  | (exist_rel var_name typ rel rel_rhs propo) := do
      let n := var_name.to_string,
      y ← to_string <$> pp rel_rhs,
      p ← to_string <$> pp propo,
      trace $ "L'hypothèse " ++ sh ++ " est de la forme « ∃ " ++ var_name.to_string ++ rel ++ y ++ ", ... »",
      trace "On peut l'utiliser avec :",
      trace ("  Par " ++ sh ++ " on obtient " ++ n ++  " tel que (" ++
          n ++ symb_to_hyp rel rel_rhs ++ " : " ++ n ++ rel ++ y ++ ") (h" ++ n ++ ": " ++ p ++ "),"),
      trace $ libres [n, n ++ symb_to_hyp rel rel_rhs, "h" ++ n]
  | (exist_simple var_name typ propo) := do
      let n := var_name.to_string,
      p ← to_string <$> pp propo,
      trace $ "L'hypothèse " ++ sh ++ " est de la forme « ∃ " ++ var_name.to_string ++ ", ... »",
      trace "On peut l'utiliser avec :",
      trace ("  Par " ++ sh ++ " on obtient " ++ n ++  " tel que (h" ++ n ++ ": " ++ p ++ "),"),
      trace $ libres [n, "h" ++ n]
  | (conjunction propo propo') := do
    p ← to_string <$> pp propo,
    p' ← to_string <$> pp propo',
    trace $ "L'hypothèse " ++ sh ++ " est de la forme « ... et ... »",
    trace "On peut l'utiliser avec :",
    trace $ "  Par " ++ sh ++ " on obtient (h₁ : " ++ p ++ ") (h₂ : " ++ p' ++ "),",
    trace $ libres ["h₁", "h₂"]
  | (disjunction propo propo') := do
    p ← to_string <$> pp propo,
    p' ← to_string <$> pp propo',
    trace $ "L'hypothèse " ++ sh ++ " est de la forme « ... ou ... »",
    trace "On peut l'utiliser avec :",
    trace $ "  On discute en utilisant " ++ sh ++ ","    
  | (impl le re lhs rhs) := do 
      l ← to_string <$> pp lhs,
      r ← to_string <$> pp rhs,
      trace $ "L'hypothèse " ++ sh ++ " est une implication",
      goal ← target,
      do {
        unify re goal,
        trace "La conclusion de cette implication est le but courant",
        trace "On peut donc utiliser cette hypothèse avec :",
        trace $ "  Par " ++ sh ++ " il suffit de montrer : " ++ r,
        trace $ "\nSi vous disposez déjà d'une preuve H de " ++ l ++ " alors on peut utiliser :",
        trace $ "  On conclut par " ++ sh ++ " appliqué à H,"} <|> 
      do {
        trace $ "La prémisse de cette implication est " ++ l,
        trace $ "Si vous avez une démonstration H de " ++ l,
        trace "vous pouvez donc utiliser cette hypothèse avec :",
        trace $ "  Par " ++ sh ++ " appliqué à H on obtient H' : " ++ r ++ ",",
        trace $ libre "H'"  }
  | (ssi le re lhs rhs) := do 
      l ← to_string <$> pp lhs,
      r ← to_string <$> pp rhs,
      trace $ "L'hypothèse " ++ sh ++ " est une équivalence",
      trace $ "On peut s'en servir pour remplacer le membre de gauche (c'est à dire " ++ l ++ 
              ") par le membre de droite  (c'est à dire " ++ r ++ ") dans le but par :",
      trace $ "  On réécrit via " ++ sh ++ ",",
      trace $ "On peut s'en servir pour remplacer le membre de droite dans par le membre de gauche dans le but par :",
      trace $ "  On réécrit via ←" ++ sh ++ ",",
      trace $ "On peut aussi effectuer de tels remplacements dans une hypothèse " ++ sh ++ "' par",
      trace $ "  On réécrit via " ++ sh ++ " dans "++ sh ++ "',",
      trace $ "ou",
      trace $ "  On réécrit via ←" ++ sh ++ " dans "++ sh ++ "',"
  | (egal le re) := do 
      l ← to_string <$> pp le,
      r ← to_string <$> pp re,
      trace $ "L'hypothèse " ++ sh ++ " est une égalité",
      ex : bool ← lock_tactic_state $ (exact eh >> pure tt) <|> pure ff,
      if ex then
          trace $ "Cette égalité est exactement ce qu'il faut démontrer\n" ++
                  "On peut l'utiliser avec :\n" ++
                  "  On conclut par " ++ sh ++ ","
      else 
        do {lin : bool ← lock_tactic_state $ (linarith ff tt [to_pexpr eh] >> pure tt) <|> pure ff,
        if lin then 
          trace $ "Le but courant en découle immédiatement\n" ++
                  "On peut l'utiliser avec :\n" ++
                  "  On conclut par " ++ sh ++ "," 
        else
          do       
          trace $ "On peut s'en servir pour remplacer le membre de gauche (c'est à dire " ++ l ++ 
                  ") par le membre de droite  (c'est à dire " ++ r ++ ") dans le but par :",
          trace $ "  On réécrit via " ++ sh ++ ",",
          trace $ "On peut s'en servir pour remplacer le membre de droite dans par le membre de gauche dans le but par :",
          trace $ "  On réécrit via ← " ++ sh ++ ",",
          trace $ "On peut aussi effectuer de tels remplacements dans une hypothèse " ++ sh ++ "' par",
          trace $ "  On réécrit via " ++ sh ++ " dans "++ sh ++ "',",
          trace $ "ou",
          trace $ "  On réécrit via ← " ++ sh ++ " dans "++ sh ++ "',\n",
          trace $ "On peut aussi s'en servir comme étape dans un calcul, ou bien combinée linéairement à d'autres par :\n" ++
                  "  On combine [" ++ sh ++ ", ...]," }
  | (ineq le rel re) := do 
      l ← to_string <$> pp le,
      r ← to_string <$> pp re,
      trace $ "L'hypothèse " ++ sh ++ " est une inégalité",
      ex : bool ← lock_tactic_state $ (exact eh >> pure tt) <|> pure ff,
      if ex then
          trace $ "Cette inégalité est exactement ce qu'il faut démontrer\n" ++
                  "On peut l'utiliser avec :\n" ++
                  "  On conclut par " ++ sh ++ ","
      else 
        do {lin : bool ← lock_tactic_state $ (linarith ff tt [to_pexpr eh] >> pure tt) <|> pure ff,
        if lin then 
          trace $ "Le but courant en découle immédiatement\n" ++
                  "On peut l'utiliser avec :\n" ++
                  "  On conclut par " ++ sh  ++ ","
        else
          trace $ "On peut s'en servir comme étape dans un calcul, ou bien combinée linéairement à d'autres par :\n" ++
                  "  On combine [" ++ sh ++ ", ...],"
            }
  | (prop `(false)) := do 
      trace $ "Cette hypothèse est une contradiction.\n" ++
              "On peut en déduire tout ce qu'on veut par :\n" ++
              "  Montrons une contradiction,\n  On conclut par " ++ sh ++ ","
  | (prop e) := do 
      trace "Je n'ai rien à déclarer à propos de cette hypothèse."
  | (data e) := do
      t ← to_string <$> pp e,
      trace $ "L'objet " ++ sh ++ match t with
      | "ℝ" := " est un nombre réel fixé."
      | "ℕ" := " est un nombre entier naturel fixé."
      | "ℤ" := " est un nombre entier relatif fixé."
      | s := " : " ++ s ++ " est fixé."
      end
  end
 
| none := do 
  goal ← target,
  g ← parse goal,
  match g with
  | (forall_rel var_name typ rel rel_rhs propo) := do
      py ← pp rel_rhs,
      let commun := var_name.to_string ++ rel ++ py.to_string ++ ",",
      trace $ "Le but commence par « ∀ " ++ commun ++ " »",
      trace "Une démonstration directe commence donc par :",
      trace $ "  Soit " ++ commun ++ ","
  | (forall_simple var_name typ propo) := do
      let n := var_name.to_string,
      t ← to_string <$> pp typ,
      trace $ "Le but commence par « ∀ " ++ var_name.to_string ++ " : " ++ t ++ ", »",
      trace "Une démonstration directe commence donc par :",
      trace $ "  Soit " ++ var_name.to_string ++ " : " ++ t ++ ","
  | (exist_rel var_name typ rel rel_rhs propo) := do
      let n := var_name.to_string,
      let n₀ := n ++ "₀",
      let nn₀ := mk_simple_name n₀,
      tgt ← to_string <$> pp (propo.rename (mk_simple_name n) nn₀),
      t ← to_string <$> pp typ,
      trace $ "Le but est de la forme « ∃ " ++ n ++ ", ... »",
      trace "Une démonstration directe commence donc par :",
      trace $ "  Montrons que " ++ n₀ ++ " convient : " ++ tgt ++ ",",
      trace $ "en remplaçant " ++ n₀ ++ " par " ++ describe t
  | (exist_simple var_name typ propo) := do
      let n := var_name.to_string,
      let n₀ := n ++ "₀",
      let nn₀ := mk_simple_name n₀,
      tgt ← to_string <$> pp (propo.rename (mk_simple_name n) nn₀),
      t ← to_string <$> pp typ,
      trace $ "Le but est de la forme « ∃ " ++ n ++ ", ... »",
      trace "Une démonstration directe commence donc par :",
      trace $ "  Montrons que " ++ n₀ ++ " convient : " ++ tgt ++ ",",
      trace $ "en remplaçant " ++ n₀ ++ " par " ++ describe t
  | (conjunction propo propo') := do
    p ← to_string <$> pp propo,
    p' ← to_string <$> pp propo',
    trace $ "Le but est de la forme « ... et ... »",
    trace "Une démonstration directe commence donc par :",
    trace $ "  Montrons que " ++ p ++ ",",
    trace $ "Une fois cette première démonstration achevée, il restera à montrer que " ++ p'
  | (disjunction propo propo') := do
    p ← to_string <$> pp propo,
    p' ← to_string <$> pp propo',
    trace $ "Le but est de la forme « ... ou ... »",
    trace "Une démonstration directe commence donc par annoncer quelle alternative va être démontrée :",
    trace $ "  Montrons que " ++ p ++ ",",
    trace $ "ou bien :",
    trace $ "  Montrons que " ++ p' ++ ","
  | (impl le re lhs rhs) := do 
      l ← pp lhs,
      trace $ "Le but est une implication « " ++ l.to_string ++ " → ... »",
      trace "Une démonstration directe commence donc par :",
      trace $ "  Supposons hyp : " ++ l.to_string ++ ", ",
      trace "où hyp est un nom disponible au choix."
  | (ssi le re lhs rhs) := do 
      l ← to_string <$> pp lhs,
      r ← to_string <$> pp rhs,  
      trace "Le but est une équivalence. On peut annoncer la démonstration de l'implication de la gauche vers la droite par :",
      trace $ " Montrons que " ++ l ++ " → " ++ r ++ ",",
      trace $ "Une fois cette première démonstration achevée, il restera à montrer que " ++ r ++ " → " ++ l
  | (egal le re) := do
      l ← to_string <$> pp le,
      r ← to_string <$> pp re,
      trace $ "Le but est une égalité\n" ++
              "On peut la démontrer par réécriture avec la commande `On réécrit via`\n" ++
              "ou bien commencer un calcul par\n" ++
              "  calc " ++ l ++ " = sorry : by { sorry }\n" ++
              "  ... = " ++ r ++ " : by { sorry },\n" ++
              "On peut bien sûr utiliser plus de lignes intermédiaires.\n" ++
              "Attention à ne pas mettre de virgule à la fin des lignes intermédiaires.\n\n" ++
              "On peut aussi tenter des combinaisons linéaires d'hypothèses hyp₁ hyp₂... avec\n" ++
              "  On combine [hyp₁, hyp₂],"
  | (ineq le rel re) := do
      l ← to_string <$> pp le,
      r ← to_string <$> pp re,
      trace $ "Le but est une inégalité\n" ++
              "On peut commencer un calcul par\n" ++
              "  calc " ++ l ++ rel ++ "sorry : by { sorry }\n" ++
              "  ... = " ++ r ++ " : by { sorry },\n" ++
              "On peut bien sûr utiliser plus de lignes intermédiaires.\n" ++
              "La dernière ligne du calcul n'est pas forcément une égalité, cela peut être une inégalité.\n" ++
              "De même la première ligne peut être une égalité. Au total les symboles de relations\n" ++
              "doivent s'enchaîner pour donner " ++ rel ++ "\n" ++
              "Attention à ne pas mettre de virgule à la fin des lignes intermédiaires.\n\n" ++
              "On peut aussi tenter des combinaisons linéaires d'hypothèses hyp₁ hyp₂... avec\n" ++
              "  On combine [hyp₁, hyp₂],"
  | (prop `(false)) := do 
      trace $ "Le but est de montrer une contradiction.\n" ++
              "On peut par exemple appliquer une hypothèse qui est une négation" ++
              "c'est à dire, par définition, de la forme P → false."
  | (prop e) := do 
      trace "Pas d'idée"
  | (data e) := do
      trace "Pas d'idée"
  end
end

namespace tactic.interactive
setup_tactic_parser
open tactic

meta def aide (i : parse ident?) : tactic unit :=
focus1 (tactic.aide i)

end tactic.interactive

example (P Q : ℕ → Prop) (h : ∀ n, P n → Q n) (h' : P 2) : Q 2 :=
begin
  aide h,
  exact h 2 h'
end

example (P : ℕ → Prop) (h : ∀ n, P n) : P 2 :=
begin
  aide h,
  exact h 2
end


example (P Q : ℕ → Prop) (h : P 1 → Q 2) (h' : P 1) : Q 2 :=
begin
  aide h,
  exact h h'
end

example (P Q : ℕ → Prop) (h : P 1 → Q 2) : true :=
begin
  aide h,
  trivial
end

example (P Q : ℕ → Prop) (h : P 1 ∧ Q 2) : true :=
begin
  aide h,
  trivial
end

example (P Q : ℕ → Prop) (h : (∀ n ≥ 2, P n) ↔  ∀ l, Q l) : true :=
begin
  aide h,
  trivial
end

example : true ∧ 1 = 1 :=
begin
  aide,
  exact ⟨trivial, rfl⟩
end

example (P Q : ℕ → Prop) (h : P 1 ∨ Q 2) : true :=
begin
  aide h,
  trivial
end


example : true ∨ false :=
begin
  aide,
  left,
  trivial
end

example (P : Prop) (h : P) : true :=
begin
  aide h,
  trivial
end

example (P : ℕ → ℕ → Prop) (k l n : ℕ) (h : l - n = 0 → P l k) : true :=
begin
  aide h,
  aide k,
  trivial
end

example (P : ℕ → ℕ → Prop) (h : ∀ k ≥ 2, ∃ n ≥ 3, ∀ l, l - n = 0 → P l k) : true :=
begin
  aide h,
  trivial
end

example (P : ℕ → Prop) (h : ∃ n ≥ 5, P n) : true :=
begin
  aide h,
  trivial
end


example (P : ℕ → ℕ → Prop) (h : ∀ k ≥ 2, ∃ n ≥ 3, P n k) : true :=
begin
  aide h,
  trivial
end


example (P : ℕ → Prop) (h : ∃ n : ℕ, P n) : true :=
begin
  aide h,
  trivial
end

example (P : ℕ → ℕ → Prop) (h : ∀ k, ∃ n : ℕ, P n k) : true :=
begin
  aide h,
  trivial
end

example (P : ℕ → ℕ → Prop) (h : ∀ k ≥ 2, ∃ n : ℕ, P n k) : true :=
begin
  aide h,
  trivial
end


example (P : ℕ → Prop): ∃ n : ℕ, P n → true :=
begin
  aide,
  use 0,
  tauto
end

example (P Q : Prop) (h : Q) : P → Q :=
begin
  aide,
  exact λ _, h,
end

example : ∀ n ≥ 0, true :=
begin
  aide,
  intros,
  trivial
end

example : ∀ n : ℕ, 0 ≤ n :=
begin
  aide,
  exact nat.zero_le 
end
