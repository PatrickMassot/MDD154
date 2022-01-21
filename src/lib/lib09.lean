import lib.m154 analysis.specific_limits topology.sequences
open m154

def majorant (A : set ℝ) (x : ℝ) := ∀ a ∈ A, a ≤ x
def borne_sup (A : set ℝ) (x : ℝ) := majorant A x ∧ ∀ y, majorant A y → x ≤ y

lemma lt_sup {A : set ℝ} {x : ℝ} (hx : borne_sup A x) :
∀ y, y < x → ∃ a ∈ A, y < a :=
begin
  intro y,
  contrapose!,
  exact hx.right y,
end

lemma inferieur_si_inferieur_plus_eps {x y : ℝ} :
  (∀ ε > 0, y ≤ x + ε) →  y ≤ x :=
begin
  contrapose!,
  intro h,
  use (y-x)/2,
  split,
    linarith,
  linarith,
end

-- Si u tend vers x et u_n ≤ y pour tout n alors x ≤ y.
lemma lim_le {x y : ℝ} {u : ℕ → ℝ} (hu : limite_suite u x)
  (ineg : ∀ n, u n ≤ y) : x ≤ y :=
begin
  apply inferieur_si_inferieur_plus_eps,
  intros ε ε_pos,
  cases hu ε ε_pos with N hN,
  specialize hN N (by linarith),
  specialize ineg N,
  rw abs_inferieur_ssi at hN,
  linarith,
end

def limite_infinie_suite (u : ℕ → ℝ) := ∀ A, ∃ N, ∀ n ≥ N, u n ≥ A

lemma limite_infinie_pas_finie {u : ℕ → ℝ} :
  limite_infinie_suite u → ∀ x, ¬ limite_suite u x :=
begin
  intros lim_infinie x lim_x,
  cases lim_x 1 (by linarith) with N hN,
  cases lim_infinie (x+2) with N' hN',
  let N₀ := max N N',
  specialize hN N₀ (inferieur_max_gauche _ _),
  specialize hN' N₀ (inferieur_max_droite _ _),
  rw abs_inferieur_ssi at hN,
  linarith,
end

lemma inv_succ_pos : ∀ n : ℕ, 1/(n + 1 : ℝ) > 0 :=
by apply nat.one_div_pos_of_nat

lemma limite_inv_succ :  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, 1/(n + 1 : ℝ) ≤ ε :=
begin
  convert metric.tendsto_at_top.mp (tendsto_one_div_add_at_top_nhds_0_nat),
  apply propext,
  simp only [real.dist_eq, sub_zero],
  split,
    intros h ε ε_pos,
    cases h (ε/2) (by linarith) with N hN,
    use N,
    intros n hn,
    rw abs_of_pos (inv_succ_pos n),
    specialize hN n hn,
    linarith,
  intros h ε ε_pos,
  cases h ε (by linarith) with N hN,
  use N,
  intros n hn,
  specialize hN n hn,
  rw abs_of_pos (inv_succ_pos n) at hN,
  linarith,
end

lemma lim_constante (x : ℝ) : limite_suite (λ n, x) x :=
λ ε ε_pos, ⟨0, λ _ _, by simp [le_of_lt ε_pos]⟩

lemma limite_si_inferieur_un_sur {u : ℕ → ℝ} {x : ℝ} (h : ∀ n, |u n - x| ≤ 1/(n+1)) :
limite_suite u x :=
begin
  intros ε ε_pos,
  rcases limite_inv_succ ε ε_pos with ⟨N, hN⟩,
  use N,
  intros n hn,
  specialize h n,
  specialize hN n hn,
  linarith,
end

lemma lim_plus_un_sur (x : ℝ) : limite_suite (λ n, x + 1/(n+1)) x :=
limite_si_inferieur_un_sur (λ n, by rw abs_of_pos ; linarith [inv_succ_pos n])

lemma lim_moins_un_sur (x : ℝ) : limite_suite (λ n, x - 1/(n+1)) x :=
begin
  refine limite_si_inferieur_un_sur (λ n, _),
  rw [show x - 1 / (n + 1) - x = -(1/(n+1)), by ring, abs_neg,  abs_of_pos],
  linarith [inv_succ_pos n]
end

lemma gendarmes {u v w : ℕ → ℝ} {l : ℝ}
(lim_u : limite_suite u l) (lim_w : limite_suite w l)
(hu : ∀ n, u n ≤ v n) (hw : ∀ n, v n ≤ w n)  : limite_suite v l :=
begin
  intros ε ε_pos,
  cases lim_u ε ε_pos with N hN,
  cases lim_w ε ε_pos with N' hN',
  use max N N',
  intros n hn,
  rw superieur_max_ssi at hn,
  cases hn with hn hn',
  specialize hN n (by linarith),
  specialize hN' n (by linarith),
  specialize hu n,
  specialize hw n,
  rw abs_inferieur_ssi at *,
  cases hN with hNl hNd,
  cases hN' with hN'l hN'd,
  split,
  -- Ici linarith peut finir, mais sur papier on écrirait
  calc -ε ≤ u n - l : by linarith
      ... ≤ v n - l : by linarith,
  calc v n - l ≤ w n - l : by linarith
      ... ≤ ε : by linarith,
end


-- Dans la suite, φ désignera toujours une fonction de ℕ dans ℕ
variable { φ : ℕ → ℕ}
variables {u : ℕ → ℝ} {l : ℝ}
open filter

/-- Si `u` tend vers `l` alors toutes ses suites extraites tendent vers `l`. -/
lemma limite_extraction_si_limite (h : limite_suite u l) (hφ : extraction φ) :
limite_suite (u ∘ φ) l :=
begin
  intros ε ε_pos,
  cases h ε ε_pos with N hN,
  use N,
  intros n hn,
  apply hN,
  calc N ≤ n   : hn -- on peut écrire « by exact hn » si on a un clavier solide
     ... ≤ φ n : extraction_superieur_id hφ n, -- idem
end

def segment (a b : ℝ) := {x | a ≤ x ∧ x ≤ b}

notation `[`a `, ` b `]` := segment a b

lemma bolzano_weierstrass {a b : ℝ} {u : ℕ → ℝ} (h : ∀ n, u n ∈ [a, b]) :
∃ c ∈ [a, b], valeur_adherence u c :=
begin
  rcases (is_compact_Icc : is_compact ([a, b])).tendsto_subseq h with ⟨c, c_in, φ, hφ, lim⟩,
  use [c, c_in, φ, hφ],
  simp_rw [metric.tendsto_nhds, eventually_at_top, real.dist_eq] at lim,
  intros ε ε_pos,
  rcases lim ε ε_pos with ⟨N, hN⟩,
  use N,
  intros n hn,
  exact le_of_lt (hN n hn)
end

lemma limite_suite_id : ∀ A : ℝ, ∃ N : ℕ, ∀ n ≥ N, (n : ℝ) ≥ A:=
begin
  intro A,
  cases exists_nat_gt A with N hN,
  use N,
  intros n hn,
  have : (n : ℝ) ≥ N, exact_mod_cast hn,  --- pfff
  linarith,
end

open real

lemma sup_segment {a b : ℝ} {A : set ℝ} (hnonvide : ∃ x, x ∈ A) (h : A ⊆ [a, b]) :
  ∃ x ∈ [a, b], borne_sup A x :=
begin
  have b_maj :  ∀ (y : ℝ), y ∈ A → y ≤ b,
    from λ y y_in, (h y_in).2,
  have Sup_maj : majorant A (Sup A),
    from (cSup_le_iff ⟨b, b_maj⟩ hnonvide).mp le_rfl,
  refine ⟨Sup A, _, _⟩,
  { split,
    { cases hnonvide with x x_in,
      exact le_trans (h x_in).1 (Sup_maj _ x_in) },
    { exact cSup_le hnonvide b_maj } },
  { use Sup_maj,
    intros y y_in,
    exact cSup_le hnonvide y_in },
end
