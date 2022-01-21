import .commun
import .tokens

namespace tactic
setup_tactic_parser

meta def Fait_parser : lean.parser (name × pexpr × option pexpr) :=
with_desc "... : ... (par ... (appliqué à ...))" $
do n ← ident <* tk ":",
   enonce ← texpr,
   do { dem ← tk "par" *> texpr,
        args ← applique_a_parser,
        pure (n, enonce, some (pexpr_mk_app dem args)) } <|> 
   pure (n, enonce, none)

/--
Annonce un énoncé intermédiaire (et le démontre immédiatement si « par » est utilisé).
-/
@[interactive]
meta def tactic.interactive.Fait : parse Fait_parser → tactic unit
| (n, enonce, some prf) := do verifie_nom n,
                              eenonce ← i_to_expr enonce,
                              assert n eenonce,
                              conclure prf []
                              
| (n, enonce, none) := do verifie_nom n,
                          i_to_expr enonce >>= tactic.assert n,
                          skip

end tactic

example (n : ℕ) : n + n + n = 3*n :=
begin
  Fait clef : n + n = 2*n,
  by ring,
  ring,
end

example (n : ℤ) (h : 0 < n) : true :=
begin
  Fait clef : 0 < 2*n par h, 
  success_if_fail { Fait clef : 0 < 2*n par h }, 
  Fait clefbis : 0 < 2*n par mul_pos appliqué à [zero_lt_two, h],
  trivial
end

example (n : ℕ) (h : 0 < n) : 0 < 2*n :=
begin
  Fait clef : 0 < 2*n par h,
  exact clef
end