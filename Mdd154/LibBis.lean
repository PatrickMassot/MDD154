import Mdd154.Lib
-- import Mathlib.Analysis.SpecificLimits.Basic
-- import Mathlib.Topology.Sequences
open m154

lemma lt_sup {A : Set ℝ} {x : ℝ} (hx : borne_sup A x) : ∀ y, y < x → ∃ a ∈ A, y < a := by
  intro y
  contrapose!
  exact hx.right y

addAnonymousFactSplittingLemma lt_sup

lemma inferieur_si_inferieur_plus_eps {x y : ℝ} :
  (∀ ε > 0, y ≤ x + ε) →  y ≤ x := by
  contrapose!
  intro h
  use (y-x)/2
  constructor
  linarith
  linarith

addAnonymousFactSplittingLemma inferieur_si_inferieur_plus_eps

-- Si u tend vers x et u_n ≤ y pour tout n alors x ≤ y.
lemma lim_le {x y : ℝ} {u : ℕ → ℝ} (hu : limite_suite u x)
  (ineg : ∀ n, u n ≤ y) : x ≤ y := by
  apply inferieur_si_inferieur_plus_eps
  intros ε ε_pos
  rcases hu ε ε_pos with ⟨N, hN⟩
  specialize hN N (by linarith)
  specialize ineg N
  rw [abs_inferieur_ssi] at hN
  linarith

addAnonymousFactSplittingLemma lim_le

lemma limite_infinie_pas_finie {u : ℕ → ℝ} :
  limite_infinie_suite u → ∀ x, ¬ limite_suite u x := by
  intros lim_infinie x lim_x
  rcases lim_x 1 (by linarith) with ⟨N, hN⟩
  rcases lim_infinie (x+2) with ⟨N', hN'⟩
  let N₀ := max N N'
  specialize hN N₀ (inferieur_max_gauche _ _)
  specialize hN' N₀ (inferieur_max_droite _ _)
  rw [abs_inferieur_ssi] at hN
  linarith


axiom inv_succ_pos : ∀ n : ℕ, 1/(n + 1 : ℝ) > 0

addAnonymousFactSplittingLemma limite_infinie_pas_finie
addAnonymousFactSplittingLemma inv_succ_pos
addAnonymousComputeLemma inv_succ_pos
addAnonymousComputeLemma abs_neg

axiom limite_inv_succ :  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, 1/(n + 1 : ℝ) ≤ ε

addAnonymousFactSplittingLemma limite_inv_succ
-- lemma limite_inv_succ :  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, 1/(n + 1 : ℝ) ≤ ε := by
--   have := Metric.tendsto_atTop.mp tendsto_one_div_add_atTop_nhds_zero_nat
--   simp only [dist_zero_right, norm_inv, Real.norm_eq_abs] at this
--   intro ε ε_pos
--   rcases this (ε/2) (by linarith) with ⟨N, hN⟩
--   use N
--   intros n hn
--   specialize hN n hn
--   rw [abs_of_pos] at hN
--   linarith
--   positivity


lemma lim_constante (x : ℝ) : limite_suite (λ _ ↦ x) x :=
λ ε ε_pos ↦ ⟨0, λ _ _ ↦ by simp [le_of_lt ε_pos]⟩

addAnonymousComputeLemma lim_constante

lemma limite_si_inferieur_un_sur {u : ℕ → ℝ} {x : ℝ} (h : ∀ n, |u n - x| ≤ 1/(n+1)) :
limite_suite u x := by
  intros ε ε_pos
  rcases limite_inv_succ ε ε_pos with ⟨N, hN⟩
  use N
  intros n hn
  specialize h n
  specialize hN n hn
  linarith


lemma lim_plus_un_sur (x : ℝ) : limite_suite (λ n ↦ x + 1/(n+1)) x :=
  limite_si_inferieur_un_sur (λ n ↦ by rw [abs_of_pos] <;> linarith [inv_succ_pos n])

addAnonymousFactSplittingLemma lim_plus_un_sur
addAnonymousComputeLemma lim_plus_un_sur

lemma lim_moins_un_sur (x : ℝ) : limite_suite (λ n ↦ x - 1/(n+1)) x := by
  refine limite_si_inferieur_un_sur (λ n ↦ ?_)
  rw [show x - 1 / (n + 1) - x = -(1/(n+1)) by ring, abs_neg, abs_of_pos]
  linarith [inv_succ_pos n]

addAnonymousFactSplittingLemma lim_moins_un_sur
addAnonymousComputeLemma lim_moins_un_sur

lemma gendarmes {u v w : ℕ → ℝ} {l : ℝ}
(lim_u : limite_suite u l) (lim_w : limite_suite w l)
(hu : ∀ n, u n ≤ v n) (hw : ∀ n, v n ≤ w n)  : limite_suite v l := by
  intros ε ε_pos
  rcases lim_u ε ε_pos with ⟨N, hN⟩
  rcases lim_w ε ε_pos with ⟨N', hN'⟩
  use max N N'
  intros n hn
  rw [superieur_max_ssi] at hn
  rcases hn with ⟨hn, hn'⟩
  specialize hN n (by linarith)
  specialize hN' n (by linarith)
  specialize hu n
  specialize hw n
  rw [abs_inferieur_ssi] at *
  cases' hN with hNl hNd
  cases' hN' with hN'l hN'd
  constructor
  -- Ici linarith peut finir, mais sur papier on écrirait
  calc -ε ≤ u n - l := by linarith
      _ ≤ v n - l := by linarith
  calc v n - l ≤ w n - l := by linarith
      _ ≤ ε := by linarith



-- Dans la suite, φ désignera toujours une fonction de ℕ dans ℕ
variable { φ : ℕ → ℕ}
variable {u : ℕ → ℝ} {l : ℝ}

/-- Si `u` tend vers `l` alors toutes ses suites extraites tendent vers `l`. -/
lemma limite_extraction_si_limite (h : limite_suite u l) (hφ : φ est une extraction) :
limite_suite (u ∘ φ) l := by
  intros ε ε_pos
  cases' h ε ε_pos with N hN
  use N
  intros n hn
  apply hN
  calc N ≤ n   := hn -- on peut écrire « by exact hn » si on a un clavier solide
     _ ≤ φ n := extraction_superieur_id hφ n -- idem

addAnonymousFactSplittingLemma limite_extraction_si_limite

def Segment (a b : ℝ) := {x | a ≤ x ∧ x ≤ b}


notation (priority := high) "["a ", " b "]" => Segment a b

lemma stupide {a b x : ℝ} (h : x ∈ [a, b]) (h' : x ≠ b) : x < b := by
  On conclut par lt_of_le_of_ne en utilisant h.2 et h'

addAnonymousFactSplittingLemma stupide

axiom bolzano_weierstrass {a b : ℝ} {u : ℕ → ℝ} (h : ∀ n, u n ∈ [a, b]) :
∃ c ∈ [a, b], valeur_adherence u c
-- lemma bolzano_weierstrass {a b : ℝ} {u : ℕ → ℝ} (h : ∀ n, u n ∈ [a, b]) :
-- ∃ c ∈ [a, b], valeur_adherence u c := by
--   rcases (isCompact_Icc : IsCompact ([a, b])).tendsto_subseq h with ⟨c, c_in, φ, hφ, lim⟩
--   use c, c_in, φ, hφ
--   simp_rw [Metric.tendsto_nhds, eventually_atTop, Real.dist_eq] at lim
--   intros ε ε_pos
--   rcases lim ε ε_pos with ⟨N, hN⟩
--   use N
--   intros n hn
--   exact le_of_lt (hN n hn)


axiom limite_suite_id : ∀ A : ℝ, ∃ N : ℕ, ∀ n ≥ N, (n : ℝ) ≥ A

addAnonymousFactSplittingLemma limite_suite_id

open Real

axiom sup_segment {a b : ℝ} {A : Set ℝ} (hnonvide : ∃ x, x ∈ A) (h : A ⊆ [a, b]) :
  ∃ x ∈ [a, b], borne_sup A x

addAnonymousFactSplittingLemma sup_segment
addAnonymousFactSplittingLemma funext

def continue_en (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε

notation3:50 f:80 " est continue en " x:60 => continue_en f x

configureUnfoldableDefs «croissante» «decroissante» «paire» «impaire»
  «valeur_adherence» «limite_suite» «surjective» «injective» «pair» «impair» «extraction» suite_cauchy limite_infinie_suite continue_en

