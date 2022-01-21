import tactic
import .tokens
import .commun

setup_tactic_parser

namespace tactic

meta def intro_obj (n : name) : tactic expr :=
do t ← target,
   if expr.is_pi t ∨ expr.is_let t then do 
     e ← intro_core n,
     t ← infer_type e,
     mwhen (is_prop t) failed,
     pure e
   else do
     whnf_target,
     e ← intro_core n, 
     t ← infer_type e,
     mwhen (is_prop t) failed,
     pure e
   


meta def Soit1 : introduced → tactic unit 
| (introduced.typed n t)   := do verifie_nom n,
                                 et ← to_expr t,
                                 e ← intro_obj n <|> fail "Il n'y a pas d'objet à introduire ici.",
                                 change_core et e
| (introduced.bare n)      := do verifie_nom n,
                                 intro_obj n <|> fail "Il n'y a pas d'objet à introduire ici.", 
                                 skip
| (introduced.related n rel e) := do verifie_nom n,
                                 ename ← intro_obj n <|> fail "Il n'y a pas d'objet à introduire ici.",
                                 n_type ← infer_type ename,
                                 E ← match rel with
                                 | intro_rel.mem := to_expr e
                                 | _ := to_expr ```(%%e : %%n_type)
                                 end,
                                 rel_expr ← match rel with
                                 | intro_rel.lt := to_expr ``(%%ename < %%E)
                                 | intro_rel.gt := to_expr ``(%%ename > %%E)
                                 | intro_rel.le := to_expr ``(%%ename ≤ %%E)
                                 | intro_rel.ge := to_expr ``(%%ename ≥ %%E)
                                 | intro_rel.mem := to_expr ``(%%ename ∈ %%E)
                                 end,
                                 let hyp_name := if e = ``(0) then
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
                                    end,
                                 EH ← intro hyp_name,
                                 change_core rel_expr EH,
                                 skip
                                 
/-- Introduit un objet ou plusieurs objets pour démontrer un énoncé commençant par un quantificateur universel. -/
@[interactive]
meta def Soit (vs : parse $ with_desc "..." bracketed_intro_parser*) : tactic unit :=
vs.mmap' Soit1

end tactic

example : ∀ n > 0, ∀ k : ℕ, ∀ l ∈ (set.univ : set ℕ), true :=
begin
  Soit (n > 0) k (l ∈ set.univ),
  trivial
end

example : ∀ n > 0, ∀ k : ℕ, ∀ l ∈ (set.univ : set ℕ), true :=
begin
  Soit n,
  success_if_fail { Soit h },
  intro hn,
  Soit k (l ∈ set.univ),
  trivial
end

example : ∀ n > 0, ∀ k : ℕ, true :=
begin
  Soit (n > 0),
  success_if_fail { Soit n },
  Soit k,
  trivial
end

example : ∀ n > 0, ∀ k : ℕ, true :=
begin
  Soit n > 0,
  success_if_fail { Soit n },
  Soit k,
  trivial
end

example (k l : ℕ) : ∀ n ≤ k + l, true :=
begin
  Soit n ≤ k + l,
  trivial,
end

example (A : set ℕ) : ∀ n ∈ A, true :=
begin
  Soit n ∈ A,
  trivial
end