import lib.lib09

open m154

/-
Le bouquet final

Cette feuille utilise tout le cours de MDD 154 pour démontrer de nombreux
théorèmes parmi les plus subtils de Math 101 : la caractérisation
séquentielle des bornes supérieures, l'équivalence entre continuité
séquentielle et continuité, le fait que toute fonction continue sur un segment
est majorée et atteint son maximum, et enfin le théorème des valeurs
intermédiaires.

Il est inutile d'aborder cette feuille sans être à l'aise avec les feuilles
précédentes. Réviser les feuilles précédentes et poser des questions est toujours 
une bonne idée.

On commence par un échauffement, une variante du

  lim_le (hu : limite_suite u x) (ineg : ∀ n, u n ≤ y) : x ≤ y

de la feuille 8, avec l'autre inégalité et seulement à partir d'un certain rang.

On pourra utiliser les lemmes habituels :

  `abs_inferieur_ssi (x y : ℝ) : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y`

  `superieur_max_ssi (p q r) : r ≥ max p q  ↔ r ≥ p ∧ r ≥ q`

  `inferieur_max_gauche p q : p ≤ max p q`

  `inferieur_max_droite p q : q ≤ max p q`

ainsi que le lemme

  `inferieur_si_inferieur_plus_eps : (∀ ε > 0, y ≤ x + ε) →  y ≤ x`

démontré dans la feuille 8
-/

-- Si u tend vers x et y ≤ u_n pour n assez grand n alors y ≤ x.
lemma le_lim {x y : ℝ} {u : ℕ → ℝ} (hu : limite_suite u x)
  (ineg : ∃ N, ∀ n ≥ N, y ≤ u n) : y ≤ x :=
begin
  sorry
end

/-
Le premier objectif sérieux de cette feuille est de démontrer la caractérisation
séquentielle des bornes supérieures. Pour cela, et pour les objectifs suivants,
nous aurons besoin de pas mal de choses des feuilles précédentes, et de
quelques extras.

Nous avons démontré dans la feuille 5 qu'une suite constante converge vers
sa valeur :

  `lim_constante (x : ℝ) : limite_suite (λ n, x) x`

et le théorème des gendarmes :

  `gendarmes (lim_u : limite_suite u l) (lim_w : limite_suite w l)`
    `(hu : ∀ n, u n ≤ v n) (hw : ∀ n, v n ≤ w n)  : limite_suite v l`

Dans la feuille 8, nous avons introduit les deux définitions :

  Le réel x est un majorant de l'ensemble de réels A :
  `def majorant (A : set ℝ) (x : ℝ) := ∀ a ∈ A, a ≤ x`

  Le réel x est une  borne supérieure de l'ensemble de réels A :
  `def borne_sup (A : set ℝ) (x : ℝ) := majorant A x ∧ ∀ y, majorant A y → x ≤ y`

et montré que si un réel x est borne supérieure d'un ensemble de réels A alors,
pour tout y, si y < x alors il existe a dans A strictement plus grand que y.

  `lt_sup (hx : borne_sup A x) : ∀ y, y < x → ∃ a ∈ A, y < a`

Dans les exercices suivants, on pourra aussi utiliser les lemmes

  `inv_succ_pos : ∀ n : ℕ, 1/(n + 1 : ℝ) > 0`

  `limite_inv_succ :  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, 1/(n + 1 : ℝ) ≤ ε`

et les conséquences faciles suivantes de limite_inv_succ :

  `limite_si_inferieur_un_sur (h : ∀ n, |u n - x| ≤ 1/(n+1)) : limite_suite u x`

  `lim_plus_un_sur (x : ℝ) : limite_suite (λ n, x + 1/(n+1)) x`

  `lim_moins_un_sur (x : ℝ) : limite_suite (λ n, x - 1/(n+1)) x`

La structure de la démonstration est offerte. Les accolades servent à
délimiter les objectifs intermédiaires, tout en faisant provisoirement
disparaître l'affichage des objectifs en attente. Il ne faut surtout pas
les supprimer, sous peine de se perdre irrémédiablement.

Enfin on notera l'apparition dans la structure de démonstration ci-dessous
de la commande `Par ... on choisit ... tel que`. Cette commande est décrite 
dans la dernière section du chapitre 3 du cours, intitulée 
« Utilisation d'un ∀x, ∃y et axiome du choix »
(qu'il convient donc de relire ou de lire), mais n'était pas encore apparue
dans les exercices.
-/

-- Un réel x est borne supérieure d'un ensemble de réels A ssi il est
-- majorant de A et il existe une suite d'éléments de A qui tend vers x.
lemma borne_sup_ssi (A : set ℝ) (x : ℝ) :
(borne_sup A x) ↔ (majorant A x ∧ ∃ u : ℕ → ℝ, limite_suite u x ∧ ∀ n, u n ∈ A) :=
begin
  Montrons que (borne_sup A x) → (majorant A x ∧ ∃ u : ℕ → ℝ, limite_suite u x ∧ ∀ n, u n ∈ A),
  { Supposons h : borne_sup A x,
    Montrons que majorant A x,
    { 
  sorry
    },
    Montrons que ∃ (u : ℕ → ℝ), limite_suite u x ∧ ∀ n, u n ∈ A,
    { Fait F1 : ∀ n : ℕ, ∃ a ∈ A, x - 1/(n+1) < a,
      { 
  sorry
        },
      Par F1 on choisit u tel que (hu : ∀ n, u n ∈ A) (hu' : ∀ (n : ℕ), x - 1 / (n + 1 : ℝ) < u n),
  sorry
           } },
  { 
  sorry
      },
end


/-
Les autres exercices de cette feuille utiliseront la définition de la
continuité d'une fonction de ℝ dans ℝ en un point de ℝ.
-/

/-- La fonction `f` est continue en `x₀`. -/
def continue_en (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε

-- Dans la suite, f désignera une fonction de ℝ dans ℝ, x₀ un réel et u
-- une suite de réels
variables {f : ℝ → ℝ} {x₀ : ℝ} {u : ℕ → ℝ}

/-
On commence par un échauffement concernant définition de la continuité.
-/

/-- Une fonction continue en x₀ est séquentiellement continue en x₀ -/
lemma seq_continue_si_continue (hf : continue_en f x₀)
  (hu : limite_suite u x₀) : limite_suite (f ∘ u) (f x₀) :=
begin
  sorry
end

/-
La réciproque de du lemme précédent est vraie aussi :
La continuité séquentielle en x₀ implique la continuité en x₀.
Mais la démonstration est moins courte. On pourra s'inspirer de
la démonstration de borne_sup_ssi (et du poly de math 101 !).
-/
example :
  (∀ u : ℕ → ℝ, limite_suite u x₀ → limite_suite (f ∘ u) (f x₀)) →
  continue_en f x₀ :=
begin
  sorry
end

/-
Dans la suite, étant donnés deux réels,
on utilise la notation habituelle [a, b] pour désigner le segment [a, b].
Attention, si par malheur b < a alors ce segment est vide. C'est un peu
une question de convention, mais notre définition d'un segment assure le
lemme suivant (dont l'utilisation est rarement nécessaire vu qu'il ne fait que
déplier une définition).
-/

lemma dans_segment {a b x : ℝ}  : x ∈ [a, b] ↔ a ≤ x ∧ x ≤ b :=
iff.rfl -- cette ligne signifie : « C'est équivalent par définition. »

/-
Nous avons vu dans la feuille 6 les définitions et le lemme :

Une extraction est une fonction strictement croissante de ℕ dans ℕ :

  `def extraction (φ : ℕ → ℕ) := ∀ n m, n < m → φ n < φ m`

Un réel a est valeur d'adhérence d'une suite u s'il
existe une suite extraite de u qui tend vers a.

  `def valeur_adherence (u : ℕ → ℝ) (a : ℝ) := ∃ φ, extraction φ ∧ limite_suite (u ∘ φ) a`

Toute extraction est supérieure à l'identité :

  `extraction_superieur_id : extraction φ → ∀ n, n ≤ φ n`

Et dans la feuille 8 la définition et le lemme :

La suite u tend vers +∞.

  `def limite_infinie_suite (u : ℕ → ℝ) := ∀ A, ∃ N, ∀ n ≥ N, u n ≥ A`

Si u tend vers +∞ alors u ne tend vers aucune limite finie

  `limite_infinie_pas_finie : limite_infinie_suite u → ∀ l, ¬ limite_suite u l`
-/

-- Dans la suite, φ sera une fonction de ℕ dans ℕ
variables {φ : ℕ → ℕ}


/-- Si `u` tend vers `+∞` alors toutes ses suites extraites tendent vers `+∞`. -/
lemma limite_infinie_extraction_si_limite
  (h : limite_infinie_suite u) (hφ : extraction φ) :
limite_infinie_suite (u ∘ φ) :=
begin
  sorry
end

lemma limite_infinie_gendarme {u v : ℕ → ℝ} (hu : limite_infinie_suite u)
(huv : ∀ n, u n ≤ v n) : limite_infinie_suite v :=
begin
  sorry
end

/-
Dans la suite, on pourra aussi utiliser le théorème de Bolzano-Weirstrass :

Toute suite à valeur dans un segment [a, b] admet une valeur d'adhérence
dans [a, b].

  `bolzano_weierstrass (h : ∀ n, u n ∈ [a, b]) : ∃ c ∈ [a, b], valeur_adherence u c`

Ce théorème se démontre à partir du théorème de la borne supérieure, mais il
faut construire une suite par récurrence, ce que nous n'avons pas appris à
faire dans Lean.

On pourra utiliser aussi le lemme suivant, qui lui est évident

  `limite_suite_id : limite_infinie_suite (λ n, n)`
-/

-- Toute fonction continue sur un segment y est majorée.
lemma majoree_segment {f : ℝ → ℝ} {a b : ℝ} (hf : ∀ x ∈ [a, b], continue_en f x) :
∃ M, ∀ x ∈ [a, b], f x ≤ M :=
begin
  sorry
end

/-
Pour l'exercice suivant, on pourra utiliser le lemme

  `abs_neg x : |-x| = |x|`
-/

-- Si f est continue en x₀ alors -f est aussi continue en x₀
lemma continue_opposee {f : ℝ → ℝ} {x₀ : ℝ} (h : continue_en f x₀) :
  continue_en (λ x, -f x) x₀ :=
begin
  sorry
end

-- Toute fonction continue sur un segment y est minorée.
lemma minoree_segment {f : ℝ → ℝ} {a b : ℝ} (hf : ∀ x ∈ [a, b], continue_en f x) :
∃ m, ∀ x ∈ [a, b], m ≤ f x :=
begin
  Fait clef : ∃ M, ∀ x ∈ [a, b], -f x ≤ M,
  {
  sorry
  },
  sorry
end

/-
Nous avons démontré dans la feuille 5 qu'une suite a au plus une limite :

 `unicite_limite : limite_suite u l → limite_suite u l' → l = l'`

et démontré dans la feuille 6 que,si u tend vers l alors toutes ses suites
extraites tendent vers l :

  `limite_extraction_si_limite (h : limite_suite u l) (hφ : extraction φ) :` 
    `limite_suite (u ∘ φ) l`

On admet une version du théorème de la borne supérieure (qu'on ne peut pas
démontrer sans construire les nombres réels ou admettre un autre théorème
aussi fort) :

`sup_segment {a b : ℝ} {A : set ℝ} (hnonvide : ∃ x, x ∈ A) (h : A ⊆ [a, b]) :`
  `∃ x ∈ [a, b], borne_sup A x`

Dans l'exercice suivant, il peut être utile de démontrer une inclusion
entre ensembles A et B de nombres réels.
Par définition, `A ⊆ B` signifie : `∀ x, x ∈ A → x ∈ B`.
On peut donc commencer la démonstration de A ⊆ B par « Soit (x ∈ A) »
qui fait apparaître « x : ℝ » et « x_mem : x ∈ A  » dans le contexte,
puis démontrer x ∈ B.

On remarquera aussi l'utilisation de la notation
  {x | P x}
qui désigne l'ensemble des x vérifiant le prédicat P.
Par exemple, la définition du segment [a, b] est :
`[a, b] = { x | a ≤ x ∧ x ≤ b }`

Ainsi l'énoncé `y ∈ { x | P x}` signifie `P y`, par définition.

-/

/-- Toute fonction continue sur un segment non vide y admet un maximum. -/
example {a b : ℝ} (hab : a ≤ b) (hf : ∀ x ∈ [a, b], continue_en f x) :
∃ x₀ ∈ [a, b], ∀ x ∈ [a, b], f x ≤ f x₀ :=
begin
  Par minoree_segment appliqué à hf on obtient m 
     tel que hm : ∀ (x : ℝ), x ∈ [a, b] → m ≤ f x,
  Par majoree_segment appliqué à hf on obtient M 
     tel que hM : ∀ (x : ℝ), x ∈ [a, b] → f x ≤ M,
  Posons A := {y | ∃ x ∈ [a, b], y = f x}, -- A est l'image de [a, b] par f
  Fait etape1 : ∃ y₀ ∈ [m, M], borne_sup A y₀,
  {
  sorry
  }, 
  Par etape1 on obtient y₀ tel que (y_dans : y₀ ∈ [m, M]) (y_sup : borne_sup A y₀),
  On réécrit via borne_sup_ssi dans y_sup,
  Par y_sup on obtient (y_maj : majorant A y₀) 
                       (u : ℕ → ℝ) (lim_u : limite_suite u y₀) (u_dans : ∀ n, u n ∈ A),
  Par u_dans on choisit (v : ℕ → ℝ) tel que 
    (v_dans : ∀ n, v n ∈ [a, b]) (hufv : ∀ n, u n = f (v n)),
  Fait hu_eq_comp : u = f ∘ v,
    On conclut par funext appliqué à hufv,
  sorry
end

-- Malheureusement `On combine` ne fait pas tout seul le lemme suivant
lemma stupide {a b x : ℝ} (h : x ∈ [a, b]) (h' : x ≠ b) : x < b :=
begin
  On conclut par lt_of_le_of_ne appliqué à [h.right, h'],
end
/-
Et maintenant le boss final...
-/

/-- Le théorème des valeurs intermédiaires -/
example (f : ℝ → ℝ) (hf : ∀ x, continue_en f x) (h₀ : f 0 < 0) (h₁ : f 1 > 0) :
∃ x₀ ∈ [0, 1], f x₀ = 0 :=
begin
  Posons A := { x | x ∈ [0, 1] ∧ f x < 0},
  Fait ex_x₀ : ∃ x₀ ∈ [0, 1], borne_sup A x₀,
  {
  sorry
  },
  Par ex_x₀ on obtient x₀ tel que x₀_dans x₀_sup,
  Montrons que x₀ convient,
    On conclut par x₀_dans,
  Fait fx₀_neg : f x₀ ≤ 0,
  {
  sorry
  },
  Fait x₀_1: x₀ < 1,
  {
  sorry
  },
  Fait fx₀_pos : f x₀ ≥ 0,
  { Fait dans' : ∃ N : ℕ, ∀ n ≥ N, x₀ + 1/(n+1) ∈ [0, 1],
    { Fait dans'' : ∃ N : ℕ, ∀ n≥ N, 1/(n+1 : ℝ) ≤ 1-x₀,
      {
  sorry
      },
  sorry
    },
    Fait pas_dans : ∀ n : ℕ, x₀ + 1/(n+1) ∉ A,
    -- Par définition, x ∉ A signifie « non (x ∈ A) ».
    {
  sorry
    },
    On reformule pas_dans en ∀ n : ℕ, ¬(x₀ + 1 / (n + 1 : ℝ) ∈ [0, 1] ∧ f (x₀ + 1 / (n + 1 : ℝ)) < 0),
  sorry
  },
  On combine [fx₀_pos, fx₀_neg],
end

