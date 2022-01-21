import lib.m154

open m154

section
/-
Avant d'aborder les exercices de cette section, il est important de bien
lire la dernière section du chapitre 4 du cours, intitulée
« Négation des conjonctions, disjonctions et énoncés quantifiés ».

L'objectif de cette première série de 4 exercices est de s'entraîner à
utiliser à la main la liste de formules de négation figurant dans cette
section du cours.

Le cœur de chacun de ces 4 exercices est de compléter l'énoncé,
en écrivant que des quantificateurs sans négation et sans utiliser
la définition limite_suite. On peut ensuite vérifier son énoncé en remplaçant
le « sorry » de la démonstration par « verifie ». La commande verifie
est uniquement destinée à cette série d'exercices, elle se contente de déplier
des définitions, d'appeler « On pousse la négation » et de faire un peu de nettoyage.

On rappelle aussi la définition de « u tend vers l » :

def limite_suite (u : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε
-/

-- Dans cette section, u désigne une suite de réels, f une fonction
-- de ℝ dans ℝ, et x₀ et l des réels.
variables (u : ℕ → ℝ) (f : ℝ → ℝ) (x₀ l : ℝ)

/- Négation de « u tend vers l » -/
example : ¬ (limite_suite u l) ↔
  sorry
:=
begin
  sorry
end

/- Négation de « f est continue en x₀ » -/
example : ¬ (∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ →  |f x - f x₀| ≤ ε) ↔
  sorry
:=
begin
  sorry
end

/-
Dans l'exercice suivant, il est utile de se souvenir que « ∀ x x', ... » est
l'abréviation de « ∀ x, ∀ x', ... ». De même « ∃ x x', ... » est
l'abréviation de « ∃ x, ∃ x', ... ».
-/

/- Négation de « f est uniformément continue sur ℝ » -/
example : ¬ (∀ ε > 0, ∃ δ > 0, ∀ x x', |x' - x| ≤ δ →  |f x' - f x| ≤ ε) ↔
  sorry
:=
begin
  sorry
end

/- Négation de « f est séquentiellement continue en x₀ » -/
example : ¬ (∀ u : ℕ → ℝ, limite_suite u x₀ → limite_suite (f ∘ u) (f x₀))  ↔
  sorry
:=
begin
  sorry
end
end

/-
La suite de cette feuille explore des applications élémentaires de la négation
dans l'étude des convergences de suites de réels.

On rappelle que "On combine" peut débusquer des contradictions
faciles, comme dans l'exemple suivant.
-/

example (a b : ℝ) (h : a < b) (h' : b < a) : false :=
begin
  On combine [h, h'],
end

/-
On rappelle des lemmes potentiellement utiles :

abs_inferieur_ssi (x y : ℝ) : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y

superieur_max_ssi (p q r) : r ≥ max p q  ↔ r ≥ p ∧ r ≥ q

inferieur_max_gauche p q : p ≤ max p q

inferieur_max_droite p q : q ≤ max p q
-/

/-- La suite `u` tend vers `+∞`. -/
def limite_infinie_suite (u : ℕ → ℝ) := ∀ A, ∃ N, ∀ n ≥ N, u n ≥ A

-- Si u tend vers +∞ alors u ne tend vers aucune limite finie
lemma limite_infinie_pas_finie {u : ℕ → ℝ} :
  limite_infinie_suite u → ∀ l, ¬ limite_suite u l :=
begin
  sorry
end

/-- La suite `u` est croissante. -/
def suite_croissante (u : ℕ → ℝ) := ∀ n m, n ≤ m → u n ≤ u m

-- Si u est croissante et tend vers l alors tous les u_n sont inférieurs à l.
example (u : ℕ → ℝ) (l : ℝ) (h : limite_suite u l) (h' : suite_croissante u) :
  ∀ n, u n ≤ l :=
begin
  sorry
end

/-
Dans les exercices suivants, « A : set ℝ » signifie que A est un ensemble de
nombres réels. On a la notation usuelle x ∈ A pour dire qu'un réel x est
dans l'ensemble de réels A.

La notation « ∀ x ∈ A, ...» est l'abréviation de « ∀ x, x ∈ A → ... »
(analogue à l'abréviation « ∀ ε > 0, ... »).
-/

/-- Le réel `x` est un majorant de l'ensemble de réels `A`. -/
def majorant (A : set ℝ) (x : ℝ) := ∀ a ∈ A, a ≤ x

/-- Le réel `x` est une  borne supérieure de l'ensemble de réels `A`. -/
def borne_sup (A : set ℝ) (x : ℝ) := majorant A x ∧ ∀ y, majorant A y → x ≤ y

/-
Remarque : on peut montrer facilement qu'un ensemble de réels admet au plus
une borne supérieure, mais ce ne sera pas utile ici.
-/

-- Si un réel x est borne supérieure d'un ensemble de réels A alors,
-- pour tout y, si y < x alors il existe a dans A strictement plus grand que y.
lemma lt_sup {A : set ℝ} {x : ℝ} (hx : borne_sup A x) :
∀ y, y < x → ∃ a ∈ A, y < a :=
begin
  sorry
end

/-
L'exercice suivant est une variante d'un exercice de la feuille 7.
Le but ici est de montrer son application à l'étude des limites de suites
dans le dernier exercice.
-/

-- Soit x et y deux réels. Si y ≤ x + ε pour tout ε > 0 alors y ≤ x.
lemma inferieur_si_inferieur_plus_eps {x y : ℝ} :
  (∀ ε > 0, y ≤ x + ε) →  y ≤ x :=
begin
  sorry
end

-- Si u tend vers x et u_n ≤ y pour tout n alors x ≤ y.
lemma lim_le {x y : ℝ} {u : ℕ → ℝ} (hu : limite_suite u x)
  (ineg : ∀ n, u n ≤ y) : x ≤ y :=
begin
  sorry
end

