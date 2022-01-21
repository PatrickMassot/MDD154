import .commun
import .tokens

namespace tactic
setup_tactic_parser

meta def change_head_name (n : name) : tactic unit :=
do tgt ← target,
   match tgt with
   | (expr.pi old bi t b) := change_core (expr.pi n bi t b) none 
   | _ := skip
   end

@[derive has_reflect]
meta inductive Montrons_args 
| but : pexpr → Montrons_args    -- pour change
| temoin : pexpr → option pexpr → Montrons_args -- pour use
| ex_falso : Montrons_args       -- pour exfalso
| recur : name → pexpr → Montrons_args       -- pour les récurrences

open Montrons_args

meta def Montrons_parser : lean.parser Montrons_args :=
with_desc "que ... / Montrons que ... convient / Montrons une contradiction." $
(do t ← (tk "que")?,
    e ← texpr, 
    if t.is_some then (do { t ← tk "convient",
         do { _ ← (tk ":"),
              But ← texpr,
              pure (temoin e $ some But) } <|> pure (temoin e none) } <|> 
    pure (but e)) else pure (but e)) <|>
(Montrons_args.ex_falso <$ (tk "une" *> tk "contradiction")) <|>
(Montrons_args.recur <$> ((tk "par" *> tk "récurrence") *> ident) <*> (tk ":" *> texpr))

/-- Annonce ce qu'on va démontrer. -/
@[interactive]
meta def Montrons : parse Montrons_parser → tactic unit
| (but pe) := do e ← to_expr pe, 
                do { change_core e none } <|> 
                do { left, change_core e none} <|>
                do { right, change_core e none} <|>
                do { split, change_core e none} <|>
                do { interactive.push_neg (loc.ns [none]), 
                     do { change_core e none } <|> 
                     do { `[simp only [exists_prop]], 
                          change_core e none } <|>
                     do { `[simp only [← exists_prop]], 
                          change_core e none }
                     } <|>
                fail "Ce n'est pas ce qu'il faut démontrer"
| (temoin pe But) := do tactic.use [pe],
                    try `[simp only [exists_prop]],
                    t ← target,
                    match But with
                    | (some truc) := do etruc ← to_expr truc, 
                                        change_core etruc none,
                                        skip
                    | none := skip
                    end,
                    match t with
                    | `(%%P ∧ %%Q) := split >> skip
                    | _ := skip
                    end
                    -- Les deux lignes suivantes sont supprimé en 2022 car trop imprévisible pour les étudiants
                    -- all_goals (try assumption),  
                    --all_goals (try interactive.refl),
                    

| ex_falso := tactic.interactive.exfalso
| (recur hyp pe) := focus1 (do
      verifie_nom hyp,
      e ← to_expr pe,
      match e with
      | (expr.pi n bi t b) := if t = `(ℕ) then do
              to_expr pe >>= tactic.assert hyp,
              `[refine nat.rec _ _],
              focus' [try `[dsimp only], 
                      do { change_head_name n,
                           try `[simp_rw ← nat.add_one] },
                      do { e ← get_local hyp, 
                           try (apply e) }],
              skip
          else fail "Cet énoncé doit commence par une quantification universelle sur un entier naturel."
      | _ := fail "Cet énoncé doit commence par une quantification universelle sur un entier naturel."
      end)

end tactic

example : 1 + 1 = 2 :=
begin
  Montrons que 2 = 2,
  refl
end 

variables k : nat

example : ∃ k : ℕ, 4 = 2*k :=
begin
  Montrons que 2 convient,
  ring,
end

example : ∃ k : ℕ, 4 = 2*k :=
begin
  Montrons que 2 convient : 4 = 2*2,
  ring,
end

example : true ∧ true :=
begin
  Montrons true,
  all_goals {trivial}
end

example (P Q : Prop) (h : P) : P ∨ Q :=
begin
  Montrons que P,
  exact h
end

example (P Q : Prop) (h : Q) : P ∨ Q :=
begin
  Montrons que Q,
  exact h
end

example : 0 = 0 ∧ 1 = 1 :=
begin
  Montrons que 0 = 0,
  trivial,
  Montrons que 1 = 1,
  trivial
end
example : 0 = 0 ∧ 1 = 1 :=
begin
  Montrons que 0 = 0,
  trivial,
  Montrons que 1 = 1,
  trivial
end

example : true ↔ true :=
begin
  Montrons que true → true,
  all_goals { exact id },
end

example (h : false) : 2 = 1 :=
begin
  Montrons une contradiction,
  exact h
end

example (P : ℕ → Prop) (h₀ : P 0) (h : ∀ n, P n → P (n+1)) : P 3 :=
begin
  success_if_fail { Montrons par récurrence H : true },
  Montrons par récurrence H : ∀ n, P n,
  exact h₀,
  exact h,
end

example (P : ℕ → Prop) (h₀ : P 0) (h : ∀ n, P n → P (n+1)) : true :=
begin
  Montrons par récurrence H : ∀ k, P k,
  exacts [h₀, h, trivial],
end

example : true :=
begin
  Montrons par récurrence H : ∀ l, l < l + 1,
  dec_trivial,
  intro l,
  intros hl,
  linarith,
  trivial
end

example : true :=
begin
  success_if_fail { Montrons par récurrence H : true },
  success_if_fail { Montrons par récurrence H : ∀ n : ℤ, true },
  trivial
end