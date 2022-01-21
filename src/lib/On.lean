import tactic
import topology.instances.real

import .tokens
import .compute
import .commun
import .aide

namespace tactic
setup_tactic_parser

@[derive has_reflect]
meta inductive On_args 
| exct_aply : pexpr → list pexpr → On_args -- On conclut par ... (appliqué à ...)
| aply : pexpr → On_args             -- On applique ...
| aply_at : pexpr → list pexpr → On_args  -- On applique ... à ...
| rwrite : interactive.rw_rules_t → option name → option pexpr → On_args           -- On réécrit via ... (dans ... (qui devient ...))
| rwrite_all : interactive.rw_rules_t → On_args -- On réécrit via ... partout
| compute : On_args                  -- On calcule
| compute_at : name → On_args        -- On calcule dans ...
| linar : list pexpr → On_args       -- On combine ...
| contrap (push : bool) : On_args    -- On contrapose (simplement)
| push_negation (hyp : option name) (new : option pexpr) : On_args   -- On pousse la négation (dans ... (qui devient ...))
| discussion : pexpr → On_args       -- On discute en utilisant ... [cases]
| discussion_hyp : pexpr → On_args       -- On discute selon que ... [by_cases]
| deplie : list name → On_args -- On déplie ...
| deplie_at : list name → loc → option pexpr → On_args -- On déplie ... dans ... (qui devient ...)
| rname : name → name → option loc → option pexpr → On_args -- On renomme ... en ... (dans ... (qui devient ...))
| oubli : list name → On_args -- pour clear
| reforml : name → pexpr → On_args -- pour change at

open On_args

meta def qui_devient_parser : lean.parser (option pexpr) := (tk "qui" *> tk "devient" *> texpr)?

/-- Syntax for on parser-/
meta def On_parser : lean.parser On_args :=
with_desc "conclut par ... (appliqué à ...) / On applique ... (à ...) / On calcule (dans ...) / On réécrit via ... (dans ... (qui devient ...)) / On combine ... / On contrapose / On discute selon ... / On discute selon que ... / On déplie ... (dans ... (qui devient ...)) / On renomme ... en ... (dans ... (qui devient ...)) / On oublie ... / On reformule ... en ... / On pousse la négation (dans ... (qui devient ...))" $
(exct_aply <$> (tk "conclut" *> tk "par" *> texpr) <*> applique_a_parser) <|>
(do { e ← tk "applique" *> texpr,
      aply_at e <$> (tk "à" *> pexpr_list_or_texpr) <|> pure (aply e)}) <|>
(tk "calcule" *> (compute_at <$> (tk "dans" *> ident) <|> pure compute)) <|>
(linar <$> (tk "combine" *> pexpr_list_or_texpr)) <|>
do { rules ← tk "réécrit" *> tk "via" *> interactive.rw_rules,
     rwrite_all rules <$ tk "partout" <|>
     rwrite rules <$> (tk "dans" *> ident)? <*> qui_devient_parser } <|>
do { tk "contrapose", 
     (contrap ff <$ tk "simplement") <|>
     pure (contrap tt) } <|>
push_negation <$> (tk "pousse" *> tk "la" *> tk "négation" *> (tk "dans" *> ident)?) <*> qui_devient_parser <|>
do { tk "discute",
     discussion_hyp <$> (tk "selon" *> tk "que" *> texpr) <|>
     discussion <$> (tk "en" *> tk "utilisant" *> texpr) } <|>
do { ids ← tk "déplie" *> ident*,
     do { place ← tk "dans" *> ident,
          deplie_at ids (loc.ns [place]) <$> qui_devient_parser } <|> 
     pure (deplie ids) } <|>
do { old ← tk "renomme" *> ident <* tk "en",
     new ← ident,
     do { place ← tk "dans" *> ident,
          rname old new (loc.ns [place]) <$> qui_devient_parser } <|> 
     pure (rname old new none none) } <|>
reforml <$> (tk "reformule" *> ident <* tk "en") <*> texpr <|>
oubli <$> (tk "oublie" *> ident*)


/-- Action de démonstration -/
@[interactive]
meta def On : parse On_parser → tactic unit
| (exct_aply pe l) := conclure pe l
| (aply pe) := focus1 (do 
    to_expr pe >>= apply,
    all_goals (do try assumption, nettoyage),
    skip)
| (aply_at pe pl) := do l ← pl.mmap to_expr,
                        l.mmap' (apply_arrow_to_hyp pe)  <|> interactive.specialize (pexpr_mk_app pe pl)
| (rwrite pe l new) := do interactive.rewrite pe (loc.ns [l]),
                          match (l, new) with
                          | (some hyp, some newhyp) := do ne ← get_local hyp, 
                                                          enewhyp ← to_expr newhyp,
                                                          infer_type ne >>= unify enewhyp
                          | (_, some n) := fail "On ne peut pas utiliser « qui devient » lorsqu'on réécrit via dans plusieurs endroits."
                          | (_, none) := skip
                          end
| (rwrite_all pe) := interactive.rewrite pe loc.wildcard
| compute := interactive.compute_at_goal'
| (compute_at h) := interactive.compute_at_hyp' h
| (linar le) := do le' ← le.mmap to_expr >>= split_ands,
                   linarith ff tt le' <|> fail "Combiner ces faits ce suffit pas."
| (contrap push) := do 
      `(%%P → %%Q) ← target | fail "On ne peut pas contraposer, le but n'est pas une implication",
      cp ← mk_mapp ``imp_of_not_imp_not [P, Q] <|> fail "On ne peut pas contraposer, le but n'est pas une implication",
      apply cp,
      if push then try (do unfold_defs.mmap' (λ d, try (tactic.interactive.delta [d] (loc.ns [none]))), tactic.interactive.push_neg (loc.ns [none])) else skip
| (discussion pe) := focus1 (do e ← to_expr pe,
                                `(%%P ∨ %%Q) ← infer_type e <|> fail "Cette expression n'est pas une disjonction.",
                                tgt ← target, 
                                `[refine (or.elim %%e _ _)],
                                all_goals (try (clear e)) >> skip)
| (discussion_hyp pe) := do e ← to_expr pe, 
                        `[refine (or.elim (classical.em %%e) _ _)]
| (deplie le) := interactive.unfold le (loc.ns [none])
| (deplie_at le loca new) := do interactive.unfold le loca,
                                match (loca, new) with
                                | (loc.ns [some hyp], some newhyp) := do ne ← get_local hyp, 
                                                                         enewhyp ← to_expr newhyp,
                                                                         infer_type ne >>= unify enewhyp
                                | (_, some n) := fail "On ne peut pas utiliser « qui devient » lorsqu'on déplie dans plusieurs endroits."
                                | (_, none) := skip
                                end
| (rname old new loca newhyp) := match (loca, newhyp) with
                          | (some (loc.ns [some n]), some truc) := do e ← get_local n, 
                                                                      rename_var_at_hyp old new e,
                                                                      interactive.guard_hyp_strict n truc <|>
                                                                        fail "Ce n'est pas l'expression obtenue."
                          | (some (loc.ns [some n]), none) := do e ← get_local n, 
                                                                 rename_var_at_hyp old new e
                          | _ := rename_var_at_goal old new
                          end
| (oubli l) := clear_lst l
| (reforml n pe) := do h ← get_local n, e ← to_expr pe, change_core e (some h)
| (push_negation n new) := do unfold_defs.mmap' (λ d, try (tactic.interactive.delta [d] (loc.ns [n]))), 
                              interactive.push_neg (loc.ns [n]),
                              match (n, new) with
                              | (some hyp, some stuff) := do e ← get_local hyp,
                                                             enewhyp ← to_expr stuff,
                                                             infer_type e >>= unify enewhyp
                              | (none, some stuff) := fail "On ne peut pas indiquer « qui devient » quand on pousse la négation dans le but."
                              | _ := skip
                              end


end tactic

example (P Q R : Prop) (hRP : R → P) (hR : R) (hQ : Q) : P :=
begin
  fail_if_success { On conclut par hRP appliqué à hQ },
  On conclut par hRP appliqué à hR,
end

example (P : ℕ → Prop) (h : ∀ n, P n) : P 0 :=
begin
  On conclut par h appliqué à _,
end

example (P : ℕ → Prop) (h : ∀ n, P n) : P 0 :=
begin
  On conclut par h,
end
    
    
example {a b : ℕ}: a + b = b + a :=
begin
  On calcule,
end 

example {a b : ℕ} (h : a + b - a = 0) : b = 0 :=
begin
  On calcule dans h,
  On conclut par h,
end 

variables k : nat

example (h : true) : true :=
begin
  On conclut par h,
end

example (h : ∀ n : ℕ, true) : true :=
begin
  On conclut par h appliqué à 0,
end

example (h : true → true) : true :=
begin
  On applique h,
  trivial,
end

example (h : ∀ n k : ℕ, true) : true :=
begin
  On conclut par h appliqué à [0, 1],
end

example (a b : ℕ) (h : a < b) : a ≤ b :=
begin
  On conclut par h,
end

example (a b c : ℕ) (h : a < b ∧ a < c) : a ≤ b :=
begin
  On conclut par h,
end

example (a b c : ℕ) (h : a ≤ b) (h' : b ≤ c) : a ≤ c :=
begin
  On combine [h, h'],
end

example (a b c : ℤ) (h : a = b + c) (h' : b - a = c) : c = 0 :=
begin
  On combine [h, h'],
end

example (a b c : ℕ) (h : a ≤ b) (h' : b ≤ c ∧ a+b ≤ a+c) : a ≤ c :=
begin
  On combine [h, h'],
end

example (a b c : ℕ) (h : a = b) (h' : a = c) : b = c :=
begin
  On réécrit via ← h,
  On conclut par h',
end

example (a b c : ℕ) (h : a = b) (h' : a = c) : b = c :=
begin
  On réécrit via h dans h',
  On conclut par h',
end

example (f : ℕ → ℕ) (n : ℕ) (h : n > 0 → f n = 0) (hn : n > 0): f n = 0 :=
begin
  On réécrit via h,
  exact hn
end

example (f : ℕ → ℕ) (n : ℕ) (h : ∀ n > 0, f n = 0) : f 1 = 0 :=
begin
  On réécrit via h,
  norm_num
end

example (a b c : ℕ) (h : a = b) (h' : a = c) : b = c :=
begin
  success_if_fail { On réécrit via h dans h' qui devient a = c },
  On réécrit via h dans h' qui devient b = c,
  On conclut par h',
end

example (a b c : ℕ) (h : a = b) (h' : a = c) : a = c :=
begin
  On réécrit via h partout,
  On conclut par h',
end

example (P Q R : Prop) (h : P → Q) (h' : P) : Q :=
begin
  On applique h à h',
  On conclut par h',
end

example (P Q R : Prop) (h : P → Q → R) (hP : P) (hQ : Q) : R :=
begin
  On conclut par h appliqué à [hP, hQ],
end

example (f : ℕ → ℕ) (a b : ℕ) (h : a = b) : f a = f b :=
begin
  On applique f à h,
  On conclut par h,
end

example (P : ℕ → Prop) (h : ∀ n, P n) : P 0 :=
begin
  On applique h à 0,
  On conclut par h
end

example (x : ℝ) : (∀ ε > 0, x ≤ ε) → x ≤ 0 :=
begin
  On contrapose,
  intro h,
  use x/2,
  split,
    On conclut par h, -- linarith
  On conclut par h, -- linarith
end

example (ε : ℝ) (h : ε > 0) : ε ≥ 0 := by On conclut par h
example (ε : ℝ) (h : ε > 0) : ε/2 > 0 := by On conclut par h
example (ε : ℝ) (h : ε > 0) : ε ≥ -1 := by On conclut par h
example (ε : ℝ) (h : ε > 0) : ε/2 ≥ -3 := by On conclut par h

example (x : ℝ) (h : x = 3) : 2*x = 6 := by On conclut par h

example (x : ℝ) : (∀ ε > 0, x ≤ ε) → x ≤ 0 :=
begin
  On contrapose simplement,
  intro h,
  On pousse la négation,
  On pousse la négation dans h,
  use x/2,
  split,
    On conclut par h, -- linarith
  On conclut par h, -- linarith
end

example (x : ℝ) : (∀ ε > 0, x ≤ ε) → x ≤ 0 :=
begin
  On contrapose simplement,
  intro h,
  success_if_fail { On pousse la négation qui devient 0 < x },
  On pousse la négation,
  success_if_fail { On pousse la négation dans h qui devient ∃ (ε : ℝ), ε > 0 ∧ ε < x },
  On pousse la négation dans h qui devient 0 < x,
  use x/2,
  split,
    On conclut par h, -- linarith
  On conclut par h, -- linarith
end

example : (∀ n : ℕ, false) → 0 = 1 :=
begin
  On contrapose,
  On calcule,
end

example (P Q : Prop) (h : P ∨ Q) : true :=
begin
  On discute en utilisant h,
  all_goals { intro, trivial }
end

example (P : Prop) (hP₁ : P → true) (hP₂ : ¬ P → true): true :=
begin
  On discute selon que P,
  intro h,
  exact hP₁ h,
  intro h,
  exact hP₂ h,
end

def f (n : ℕ) := 2*n

example : f 2 = 4 :=
begin
  On déplie f,
  refl,
end

example (h : f 2 = 4) : true → true :=
begin
  On déplie f dans h,
  guard_hyp_strict h : 2*2 = 4,
  exact id
end

example (h : f 2 = 4) : true → true :=
begin
  success_if_fail { On déplie f dans h qui devient 2*2 = 5 },
  On déplie f dans h qui devient 2*2 = 4,
  exact id
end

example (P : ℕ → ℕ → Prop) (h : ∀ n : ℕ, ∃ k, P n k) : true :=
begin
  On renomme n en p dans h,
  On renomme k en l dans h,
  guard_hyp_strict h : ∀ p, ∃ l, P p l,
  trivial
end

example (P : ℕ → ℕ → Prop) (h : ∀ n : ℕ, ∃ k, P n k) : true :=
begin
  On renomme n en p dans h qui devient ∀ p, ∃ k, P p k,
  success_if_fail { On renomme k en l dans h qui devient ∀ p, ∃ j, P p j },
  On renomme k en l dans h qui devient ∀ p, ∃ l, P p l,
  trivial
end

example (P : ℕ → ℕ → Prop) : (∀ n : ℕ, ∃ k, P n k) ∨ true :=
begin
  On renomme n en p,
  On renomme k en l,
  guard_target_strict (∀ p, ∃ l, P p l) ∨ true,
  right,
  trivial
end

example (a b c : ℕ) : true :=
begin
  On oublie a,
  On oublie b c,
  trivial
end

example (h : 1 + 1 = 2) : true :=
begin
  success_if_fail { On reformule h en 2 = 3 },
  On reformule h en 2 = 2,
  trivial,
end