import lib.m154

/-
Ce fichier concerne la définition de limite d'une suite (de nombres réels).
Une suite u est une fonction de ℕ dans ℝ, Lean écrit donc u : ℕ → ℝ
-/

-- Définition de « u tend vers l »
def limite_suite (u : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

/-
On notera dans la définition ci-dessus l'utilisation de « ∀ ε > 0, ... »
qui est une abbréviation de « ∀ ε, ε > 0 → ... ».

En particulier un énoncé de la forme « h : ∀ ε > 0, ... » se spécialise à
un ε₀ fixé par la commande « Par h on obtient ε₀ tel que hε₀ » où hε₀ est
une démonstration de ε₀ > 0.

Le lemme demi_pos ci-dessous sera utile pour transformer une démonstration
de ε > 0 en une démonstration de ε/2 > 0 lorsque l'on spécialise un énoncé
avec ε/2 au lieu de ε.

La démonstration n'est pas très éclairante car Lean fait le travail
automatiquement, mais c'est l'occasion de rappeler que la commande
`On conclut` accepte ce type de travail d'ajustement très direct.
-/

lemma demi_pos { ε : ℝ } : ε > 0 → ε/2 > 0 :=
begin
  Supposons hyp : ε > 0,
  On conclut par hyp,
end

-- Dans toute la suite, u, v et w sont des suites tandis que l et l' sont des
-- nombres réels
variables (u v w : ℕ → ℝ) (l l' : ℝ)

-- Si u est constante de valeur l, alors u tend vers l
example : (∀ n, u n = l) → limite_suite u l :=
begin
  sorry
end

/- Concernant les valeurs absolues, on pourra utiliser les lemmes

`abs_inferieur_ssi (x y : ℝ) : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y`

`ineg_triangle (x y : ℝ) : |x + y| ≤ |x| + |y|`

`abs_diff (x y : ℝ) : |x - y| = |y - x|`

Il est conseillé de noter ces lemmes sur une feuille car ils
peuvent être utiles dans chaque exercice.
-/

-- Si u tend vers l strictement positif, alors u n ≥ l/2 pour n assez grand.
example (hl : l > 0) : limite_suite u l → ∃ N, ∀ n ≥ N, u n ≥ l/2 :=
begin
  sorry
end

/- Concernant le maximum de deux nombres, on pourra utiliser les lemmes

`superieur_max_ssi (p q r) : r ≥ max p q  ↔ r ≥ p ∧ r ≥ q`

`inferieur_max_gauche p q : p ≤ max p q`

`inferieur_max_droite p q : q ≤ max p q`

Il est conseillé de noter ces lemmes sur une feuille car ils
peuvent être utiles dans chaque exercice.

Dans l'exemple suivant, notez particulièrement la façon dont
`demi_pos` est utilisé : sachant que `ε` est fixé et qu'on a une
hypothèse `ε_pos : ε > 0`, on peut former l'expression
`demi_pos ε_pos : ε/2 > 0`.

Notez aussi l'utilisation de `superieur_max_ssi` qui reviendra
très souvent, et la façon d'annoncer à l'avance des inégalités
intermédiaire avant de la combiner par `On combine`.
-/

-- Si u tend vers l et v tend vers l' alors u+v tend vers l+l'
example (hu : limite_suite u l) (hv : limite_suite v l') :
limite_suite (u + v) (l + l') :=
begin
  Soit ε > 0,
  Par hu appliqué à [ε/2, demi_pos ε_pos] on obtient N₁
      tel que hN₁ : ∀ n ≥ N₁, |u n - l| ≤ ε / 2,
  Par hv appliqué à [ε/2, demi_pos ε_pos] on obtient N₂
      tel que hN₂ : ∀ n ≥ N₂, |v n - l'| ≤ ε / 2,
  Montrons que max N₁ N₂ convient : ∀ n ≥ max N₁ N₂, |(u + v) n - (l + l')| ≤ ε,
  Soit n ≥ max N₁ N₂,
  On réécrit via superieur_max_ssi dans n_ge,
  Par n_ge on obtient (hn₁ : n ≥ N₁) (hn₂ : n ≥ N₂),
  Fait fait₁ : |u n - l| ≤ ε/2,
    On applique hN₁,
  Fait fait₂ : |v n - l'| ≤ ε/2,
    On conclut par hN₂ appliqué à [n, hn₂],  -- Notez la variante Lean par rapport à fait₁
  calc
  |(u + v) n - (l + l')| = |(u n - l) + (v n - l')| : by On calcule
                     ... ≤ |u n - l| + |v n - l'| : by On applique ineg_triangle
                     ... ≤  ε/2 + ε/2             : by On combine [fait₁, fait₂]
                     ... =  ε                     : by On calcule,
end

example (hu : limite_suite u l) (hw : limite_suite w l)
(h : ∀ n, u n ≤ v n)
(h' : ∀ n, v n ≤ w n) : limite_suite v l :=
begin
  sorry

end

-- La dernière inégalité dans la définition de limite peut être remplacée par
-- une inégalité stricte.
example (u l) : limite_suite u l ↔
 ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε :=
begin
  sorry
end

/- Dans l'exercice suivant, on pourra utiliser le lemme

`egal_si_abs_eps (x y : ℝ) : (∀ ε > 0, |x - y| ≤ ε) → x = y`
-/

-- Une suite u admet au plus une limite
example : limite_suite u l → limite_suite u l' → l = l' :=
begin
  sorry
end

-- Définition de « la suite u est croissante »
def croissante (u : ℕ → ℝ) := ∀ n m, n ≤ m → u n ≤ u m

-- Définition de « M est borne supérieure des termes de la suite u  »
def est_borne_sup (M : ℝ) (u : ℕ → ℝ) :=
(∀ n, u n ≤ M) ∧ ∀ ε > 0, ∃ n₀, u n₀ ≥ M - ε

-- Toute suite croissante ayant une borne supérieure tend vers cette borne
example (M : ℝ) (h : est_borne_sup M u) (h' : croissante u) :
limite_suite u M :=
begin
  sorry
end

