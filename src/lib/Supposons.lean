import tactic
import .tokens
import .commun

namespace tactic
setup_tactic_parser

@[derive has_reflect]
meta inductive Supposons_args
| regular : list pexpr → Supposons_args
| absurde : name → option pexpr → Supposons_args

meta def Supposons_parser : lean.parser Supposons_args :=
with_desc "... / Supposons par l'absurde ..." $ 
do { _ ← tk "par", _ ← tk "l'absurde", 
     n ← ident,
     do { _ ← tk ":", 
          hyp ← texpr,
          pure (Supposons_args.absurde n (some hyp)) } <|>
     pure (Supposons_args.absurde n none)} <|>
Supposons_args.regular <$> ((tk "que")? *>parse_binders tac_rbp)

private meta def supposons_core (n : name) (ty : pexpr) :=
do verifie_nom n,
   t ← target,
   when (not $ t.is_pi) whnf_target,
   t ← target,
   when (not $ t.is_arrow) $
     fail "Il n'y a rien à supposer ici, le but n'est pas une implication",
   ty ← i_to_expr ty,
   unify ty t.binding_domain,
   intro_core n >> skip

open Supposons_args

/-- Introduit une hypothèse quand le but est une implication,
ou bien démarre un raisonnement par l'absurde. -/
@[interactive]
meta def Supposons : parse Supposons_parser → tactic unit
| (regular le) := do le.mmap' (λ b : pexpr, 
                               supposons_core b.local_pp_name b.local_type)
| (absurde n hyp) := do 
    by_contradiction n, 
    try (interactive.push_neg (loc.ns [n])),
    when hyp.is_some (do 
                         Hyp ← hyp >>= to_expr,
                         let sp := simp_arg_type.symm_expr ``(exists_prop),
                         try (interactive.simp_core {} skip tt [sp] [] $ loc.ns [n]),
                         ehyp ← get_local n,
                         change_core Hyp (some ehyp))

end tactic

example : ∀ n > 0, true :=
begin
  intro n,
  success_if_fail { Supposons H : n < 0 },
  success_if_fail { Supposons n : n > 0 },
  Supposons H : n > 0,
  trivial
end

example : ∀ n > 0, true :=
begin
  intro n,
  Supposons que H : n > 0,
  trivial
end

example : ∀ n > 0, true :=
begin
  success_if_fail { Supposons n },
  intro n,
  Supposons H : n > 0,
  trivial
end

example (P Q : Prop) (h : ¬ Q → ¬ P) : P → Q :=
begin
  Supposons hP,
  Supposons par l'absurde hnQ,
  exact h hnQ hP,
end

example (P Q : Prop) (h : ¬ Q → ¬ P) : P → Q :=
begin
  Supposons hP,
  Supposons par l'absurde hnQ : ¬ Q,
  exact h hnQ hP,
end

example (P Q : Prop) (h : Q → ¬ P) : P → ¬ Q :=
begin
  Supposons hP,
  Supposons par l'absurde hnQ : Q,
  exact h hnQ hP,
end