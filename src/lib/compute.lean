import tactic.ring tactic.linarith


namespace tactic.interactive
setup_tactic_parser
open tactic.simp_arg_type

meta def lemmas : list tactic.simp_arg_type :=
[ expr ``(forall_const), 
  expr ``(not_false_iff), 
  expr ``(abs_zero),
  expr ``(add_tsub_cancel_left),
  expr ``(ge_iff_le),
  expr ``(lt_add_iff_pos_right),
  expr ``(zero_lt_one),
  expr ``(pi.add_apply)
  ]

meta def compute_at_hyp' (h : name) : tactic unit :=
let lo := loc.ns [h] in
do { ring_nf none tactic.ring.normalize_mode.horner lo <|>
norm_num1 lo  } ; try (simp_core {} skip tt lemmas [] lo *> skip)

meta def compute_at_goal' : tactic unit :=
do focus (
  tactic.to_expr ``(le_rfl) >>= tactic.exact <|>
  tactic.iterate_at_most 3 (do 
  tactic.to_expr ``(rfl) >>= tactic.exact <|> 
  ring_nf none tactic.ring.normalize_mode.horner (loc.ns [none]) <|> 
  norm_num1 (loc.ns [none]) <|>
  ((simp_core {} skip tt lemmas [] (loc.ns [none]) *> skip)))
  *> skip)
end tactic.interactive
