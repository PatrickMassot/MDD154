import tactic
import .tokens .commun

namespace tactic
setup_tactic_parser

@[derive has_reflect]
meta inductive Par_args 
-- Par fait (appliqué à args) on obtient news (tel que news')
| obtenir (fait : pexpr) (args : list pexpr) (news : list maybe_typed_ident) : Par_args
-- Par fait (appliqué à args) on obtient news (tel que news')
| choisir (fait : pexpr) (args : list pexpr) (news : list maybe_typed_ident) : Par_args
-- Par fait (appliqué à args) il suffit de montrer que buts
| appliquer (fait : pexpr) (args : list pexpr) (buts : list pexpr) : Par_args 

open Par_args

/-- Parse une liste de conséquences, peut-être vide. -/
meta def on_obtient_parser : lean.parser (list maybe_typed_ident) :=
do { news ← tk "obtient" *> maybe_typed_ident_parser*,
     news' ← (tk "tel" *> tk "que" *> maybe_typed_ident_parser*) <|> pure [], 
     pure (news ++ news') } 

/-- Parse une liste de conséquences pour `choose`. -/
meta def on_choisit_parser : lean.parser (list maybe_typed_ident) :=
do { news ← tk "choisit" *> maybe_typed_ident_parser*,
     news' ← (tk "tel" *> tk "que" *> maybe_typed_ident_parser*) <|> pure [], 
     pure (news ++ news') } 

/-- Parse un ou plusieurs nouveaux buts. -/
meta def buts_parser : lean.parser (list pexpr) :=
tk "il" *> tk "suffit" *> tk "de" *> tk "montrer" *> tk "que" *>  pexpr_list_or_texpr

/-- Parser principal pour la tactique Par. -/
meta def Par_parser : lean.parser Par_args :=
with_desc "... (appliqué à ...) on obtient ... (tel que ...) / Par ... (appliqué à ...) il suffit de montrer que ..." $
do e ← texpr,
   args ← applique_a_parser,
   do { _ ← tk "on",
       (Par_args.obtenir e args <$> on_obtient_parser) <|>
       (Par_args.choisir e args <$> on_choisit_parser) } <|>
   (Par_args.appliquer e args <$> buts_parser)

meta def verifie_type : maybe_typed_ident → tactic unit
| (n, some t) := do n_type ← get_local n >>= infer_type,
                    to_expr t >>= unify n_type  
| (n, none) := skip

/-- Récupère de l'information d'une hypothèse ou d'un lemme ou bien 
réduit le but à un ou plusieurs nouveaux buts en appliquant une 
hypothèse ou un lemme. -/
@[interactive]
meta def Par : parse Par_parser → tactic unit
| (Par_args.obtenir fait args news) := focus1 (do
    news.mmap' (λ p : maybe_typed_ident, verifie_nom p.1),
    efait ← to_expr fait,
    applied ← mk_mapp_pexpr efait args,
    if news.length = 1 then do { -- Cas où il n'y a rien à déstructurer
         nom ← match news with
         | ((nom, some new) :: t) := do enew ← to_expr new, 
                                        infer_type applied >>= unify enew,
                                        pure nom
         | ((nom, none) :: t) := pure nom
         | _ := fail "Il faut indiquer un nom pour l'information obtenue." -- ne devrait pas arriver
         end,
         hyp ← note nom none applied,
         nettoyage,
         news.mmap' verifie_type }
    else do tactic.rcases none (to_pexpr $ applied)
                  $ rcases_patt.tuple $ news.map rcases_patt_of_maybe_typed_ident, 
            nettoyage )
| (Par_args.choisir fait args news) := focus1 (do
    efait ← to_expr fait,
    applied ← mk_mapp_pexpr efait args,
    choose tt applied (news.map prod.fst),
    nettoyage,
    news.mmap' verifie_type)
| (Par_args.appliquer fait args buts) := focus1 (do
    efait ← to_expr fait,
    ebuts ← buts.mmap to_expr,
    mk_mapp_pexpr efait args >>= apply,
    vrai_buts ← get_goals, 
    let paires := list.zip vrai_buts buts,
    focus' (paires.map (λ p : expr × pexpr, do 
       `(force_type %%p _) ←  i_to_expr_no_subgoals ``(force_type %%p.2 %%p.1), skip))
    <|> fail "Ce n'est pas ce qu'il faut démontrer")

end tactic

example (P Q : (ℕ → ℕ) → Prop) (h : true ∧ ∃ u : ℕ → ℕ, P u ∧ Q u) : true :=
begin
  Par h on obtient (a : true) (u : ℕ → ℕ) (b : P u) (c : Q u),
  trivial
end

example (n : ℕ) (h : ∃ k, n = 2*k) : ∃ l, n+1 = 2*l + 1 :=
begin
  Par h on obtient k hk,
  use k,
  rw hk
end

example (n : ℕ) (h : ∃ k, n = 2*k) : ∃ l, n+1 = 2*l + 1 :=
begin
  Par h on obtient k tel que hk : n = 2*k,
  use k,
  rw hk
end

example (n : ℕ) (h : ∃ k, n = 2*k) : ∃ l, n+1 = 2*l + 1 :=
begin
  success_if_fail { 
    Par h on obtient k tel que (hk : 0 = 1), 
  },
  Par h on obtient k tel que (hk : n = 2*k),
  use k,
  rw hk
end

example (f g : ℕ → ℕ) (hf : ∀ y, ∃ x, f x = y) (hg : ∀ y, ∃ x, g x = y) : ∀ y, ∃ x, (g ∘ f) x = y :=
begin
  intro y,
  success_if_fail { Par hg appliqué à y on obtient x tel que (hx : g x = x) },
  Par hg appliqué à y on obtient x tel que (hx : g x = y),
  Par hf appliqué à x on obtient z hz,
  use z,
  change g (f z) = y,
  rw [hz, hx],
end

example (P Q : Prop) (h : P ∧ Q)  : Q :=
begin
  Par h on obtient (hP : P) (hQ : Q),
  exact hQ,
end


noncomputable example (f : ℕ → ℕ) (h : ∀ y, ∃ x, f x = y) : ℕ → ℕ :=
begin
  Par h on choisit g tel que (H : ∀ (y : ℕ), f (g y) = y),
  exact g,
end

example (P Q : Prop) (h : P → Q) (h' : P) : Q :=
begin
  Par h il suffit de montrer que P,
  exact h',
end

example (P Q R : Prop) (h : P → R → Q) (hP : P) (hR : R) : Q :=
begin
  Par h il suffit de montrer que [P, R],
  exact hP,
  exact hR
end

example (P Q : Prop) (h : ∀ n : ℕ, P → Q) (h' : P) : Q :=
begin
  success_if_fail { Par h appliqué à [0, 1] il suffit de montrer que P },
  Par h appliqué à 0 il suffit de montrer que P,
  exact h',
end

example (Q : Prop) (h : ∀ n : ℤ, n > 0 → Q)  : Q :=
begin
  Par h il suffit de montrer que (1 > 0),
  norm_num,
end
