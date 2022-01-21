import tactic
import .tokens

namespace tactic
setup_tactic_parser


@[interactive]
meta def Posons := interactive.set
end tactic

example (a b : ℕ) : ℕ :=
begin
  Posons n := max a b,
  exact n,
end
