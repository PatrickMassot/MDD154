import Mdd154.LibBis

open m154
/-
# Feuille 12 : Le bouquet final
-/

/-
Cette feuille utilise tout le cours de MDD 154 pour démontrer de nombreux
théorèmes parmi les plus subtils du cours d’analyse du premier semestre : la
caractérisation séquentielle des bornes supérieures, l'équivalence entre
continuité séquentielle et continuité, le fait que toute fonction continue sur
un segment est majorée et atteint son maximum, et enfin le théorème des valeurs
intermédiaires.

Il est inutile d'aborder cette feuille sans être à l'aise avec les feuilles
précédentes. Réviser les feuilles précédentes et poser des questions est toujours
une bonne idée.

On commence par un préliminaire tenant lieu d’échauffement : une variante du
passage à la limite dans une égalité démontré dans la feuille 11, avec l'autre
inégalité et seulement à partir d'un certain rang. Ce résultat servira dans
la démonstration du théorème des valeurs intermédiaires (on rappelle que tout énoncé
introduit par le mot clé `Exercice-lemme` devient un lemme qu’on peut utiliser
implicitement dans les exercices suivants).

On pourra utiliser les lemmes habituels :

  `∀ x y, |x| ≤ y ⇔ -y ≤ x ∧ x ≤ y`

  `∀ p q r, r ≥ max p q  ⇔ r ≥ p ∧ r ≥ q`

  `∀ p q : p ≤ max p q`

  `∀ p q : q ≤ max p q`

ainsi que le lemme

  `∀ x y, (∀ ε > 0, y ≤ x + ε) ⇒  y ≤ x`

démontré dans la feuille 11.
-/

Exercice-lemme le_lim
  "12.01 Si u tend vers x et y ≤ u_n pour n assez grand n alors y ≤ x."
Données : {x y : ℝ} {u : ℕ → ℝ}
Hypothèses : (hu : u tend vers x)
  (ineg : ∃ N, ∀ n ≥ N, y ≤ u n)
Conclusion : y ≤ x
Démonstration :
  sorry
QED

/-
Le premier objectif sérieux de cette feuille est de démontrer la caractérisation
séquentielle des bornes supérieures. Pour cela, et pour les objectifs suivants
nous aurons besoin de pas mal de choses des feuilles précédentes, et de
quelques extras.

Nous avons démontré dans la feuille 8 qu'une suite constante converge vers
sa valeur :

  `∀ (x : ℝ), (suite n ↦ x) tend vers x`


Dans la feuille 11, nous avons introduit les deux définitions :

  Le réel x est un majorant de l'ensemble de réels A :
  `x majore A` si `∀ a ∈ A, a ≤ x`

  Le réel x est une  borne supérieure de l'ensemble de réels A :
  `x est borne sup de A` si `x majore A ∧ ∀ y, y majore A ⇒ x ≤ y`

et montré que si un réel x est borne supérieure d'un ensemble de réels A alors
pour tout y, si y < x alors il existe a dans A strictement plus grand que y.

  `x est borne sup de A ⇒ (∀ y < x, ∃ a ∈ A, y < a)`

Nous avons également montré
  `(u tend vers x) ∧ (∀ n, u n ≤ y) ⇒ x ≤ y`

Dans les exercices suivants, on pourra aussi utiliser les lemmes

  `∀ n : ℕ, 1/(n + 1) > 0`

  `∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, 1/(n + 1 : ℝ) ≤ ε`

et les conséquences faciles suivantes du résultat précédent :

  `limite_si_inferieur_un_sur (h : ∀ n, |u n - x| ≤ 1/(n+1)) : u tend vers x`

  `∀ x : ℝ, (suite n ↦ x + 1/(n+1)) tend vers x`

  `∀ x : ℝ, (suite n ↦ x - 1/(n+1)) tend vers x`

À propos de l’énoncé `∀ n : ℕ, 1/(n + 1) > 0` et d’autres énoncés similaires,
il faut prendre bien garde à ne pas oublier la précision `: ℕ`. En effet Lean
n’a aucun moyen de savoir si dans `∀ n, 1/(n + 1) > 0` la quantification porte
sur tous les réels ou seulement des entiers.


On utilisera le théorème des gendarmes démontré dans une feuille précédente :

  `∀ u v w, (lim_u : u tend vers l) ∧ (lim_w : w tend vers l) ∧
    (hu : ∀ n, u n ≤ v n) ∧ (hw : ∀ n, v n ≤ w n)  ⇒ v tend vers l`

Il n’est pas commode à appliquer avec la commande comme donc on écrira pour
l’appliquer :

 Par gendarmes il suffit de montrer que
   u tend vers l et
   w tend vers l et
   ∀ n, u n ≤ v n et
   ∀ n, v n ≤ w n

avec bien sûr des suites `u` et `w` bien choisies.
Si la convergence de `u` ou `w` provient d’un des lemmes énoncés ci-dessus, on
pourra la démontrer par `On calcule`.

La structure de la démonstration est offerte.

Enfin on notera l'apparition dans la structure de démonstration ci-dessous
de la commande `Comme ... on choisit ... tel que` correspondant à l'utilisation
de l'axiome du choix (voir la section 11.1 du cours).
-/

Exercice-lemme borne_sup_vers_suite
  "12.02a Si un réel x est borne supérieure d'un ensemble de réels A alors
   il existe une suite d'éléments de A qui tend vers x."
  Données : {A : Set ℝ} {x : ℝ}
  Hypothèses : (h : x est borne sup de A)
  Conclusion : ∃ u : ℕ → ℝ, u tend vers x ∧ ∀ n, u n ∈ A
Démonstration :
 Fait F1 : ∀ n : ℕ, ∃ a ∈ A, x - 1/(n+1) < a car
  sorry
 Comme ∀ n : ℕ, ∃ a ∈ A, x - 1 / (n + 1) < a on choisit u tel que
   hu : ∀ n, u n ∈ A et hu' : ∀ (n : ℕ), x - 1 / (n + 1) < u n
 sorry
QED

/-
Montrons maintenant la réciproque qui est beaucoup plus facile.
Pour alléger la partie purement administrative de la démonstration, plutôt que de
supposer l’existence de la suite `u`, on se donne simplement `u` et ses propriétés
dans l’énoncé.
-/

Exercice-lemme borne_sup_si_majore_et_suite
  "12.02b Si un réel  est majorant de A et s’il existe une suite d'éléments de
  A qui tend vers x alors x est borne supérieure de A"
  Données : {A : Set ℝ} {x : ℝ} {u : ℕ → ℝ}
  Hypothèses : (x_maj : x majore A) (u_x : u tend vers x) (u_A : ∀ n, u n ∈ A)
  Conclusion : x est borne sup de A
Démonstration :
  sorry
QED

/-
Les autres exercices de cette feuille utiliseront la définition de la
continuité d'une fonction de ℝ dans ℝ en un point de ℝ.

`f est continue en x₀` signifie `∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ ⇒ |f x - f x₀| ≤ ε`

On commence par un échauffement concernant définition de la continuité.
-/

Exercice-lemme seq_continue_si_continue
  "12.03 Une fonction continue en x₀ est séquentiellement continue en x₀"
  Données : {f : ℝ → ℝ} {u : ℕ → ℝ}
  Hypothèses :  (hf : f est continue en x₀) (hu : u tend vers x₀)
  Conclusion : f ∘ u tend vers f x₀
Démonstration :
  sorry
QED

/-
La réciproque de du lemme précédent est vraie aussi :
La continuité séquentielle en x₀ implique la continuité en x₀.
Mais la démonstration est moins courte. On pourra s'inspirer de
la démonstration de borne_sup_ssi (et du cours du premier semestre !).
-/

Exercice "12.04 La continuité séquentielle en x₀ implique la continuité en x₀."
  Données : (f : ℝ → ℝ)
  Hypothèses :
  Conclusion :  (∀ u : ℕ → ℝ, u tend vers x₀ ⇒ f ∘ u tend vers f x₀) ⇒
  f est continue en x₀
Démonstration :
  sorry
QED

/-
Dans la suite, étant donnés deux réels
on utilise la notation habituelle [a, b] pour désigner le segment [a, b].
Attention, si par malheur b < a alors ce segment est vide. C'est un peu
une question de convention, mais notre définition d'un segment assure le
lemme suivant :
`x ∈ [a, b] ⇔ a ≤ x ∧ x ≤ b`

Nous avons vu dans la feuille 9 les définitions et le lemme :

Une extraction est une fonction strictement croissante de ℕ dans ℕ :

  `φ est une extraction` signifie `∀ n m, n < m ⇒ φ n < φ m`

Un réel a est valeur d'adhérence d'une suite u s'il
existe une suite extraite de u qui tend vers a.

  `a est valeur d'adherence de u` signifie `∃ φ, extraction φ ∧ u ∘ φ tend vers a`

Toute extraction est supérieure à l’identité :

  `∀ φ, extraction φ ⇒ ∀ n, n ≤ φ n`

Et dans la feuille 11 la définition et le lemme :

La suite u tend vers +∞.

  `u tend vers +∞` signifie `∀ A, ∃ N, ∀ n ≥ N, u n ≥ A`

Si u tend vers +∞ alors u ne tend vers aucune limite finie

  `(u tend vers +∞) ⇒ ∀ l, ¬ u tend vers l`

Le premier résultat préparatoire dont nous aurons besoin utilise uniquement
le fait que toute extraction est supérieure à l’identité.
-/

Exercice-lemme limite_infinie_extraction_si_limite
  "12.5 Si `u` tend vers `+∞` alors toutes ses suites extraites tendent vers `+∞`."
  Données : {u : ℕ → ℝ}
  Hypothèses :  (h : u tend vers +∞) (hφ : φ est une extraction)
  Conclusion : u ∘ φ tend vers +∞
Démonstration :
  sorry
QED

/-
Nous aurons également besoin d’une version du théorème des gendarmes pour les suites
qui tendent vers +∞. Il s’agit d’un énoncé plus facile que la version que nous
avons déjà vu, et elle ne nécessite aucun lemme.
-/
Exercice-lemme limite_infinie_gendarme
  "12.06 Le théorème des gendarmes pour les limites infinies."
  Données : {u v : ℕ → ℝ}
  Hypothèses : (hu : u tend vers +∞) (huv : ∀ n, u n ≤ v n)
  Conclusion : v tend vers +∞
Démonstration :
  sorry
QED

/-
Dans la suite, on pourra aussi utiliser le théorème de Bolzano-Weirstrass :

Toute suite à valeur dans un segment [a, b] admet une valeur d'adhérence
dans [a, b].

  `bolzano_weierstrass (h : ∀ n, u n ∈ [a, b]) : ∃ c ∈ [a, b], valeur_adherence u c`

Ce théorème se démontre à partir du théorème de la borne supérieure, mais il
faut construire une suite par récurrence, ce que nous n'avons pas appris à
faire dans Lean.

Cet énoncé est un peu lourd à utiliser avec la commande `Comme` donc le début de
démonstration offert ci-dessous l’invoquera avec la commande `Par` qu’il est inutile
de retenir.

On pourra utiliser l’exercice 12.5 :
  Si `u` tend vers `+∞` alors toutes ses suites extraites tendent vers `+∞`."
et l’exercice 12.03 :
  Une fonction continue en x₀ est séquentiellement continue en x₀
ainsi que le résultat de la feuille 11 :
  `(u tend vers +∞) ⇒ ∀ l, ¬ u tend vers l`

On pourra utiliser aussi le lemme suivant, qui lui est évident
  `(suite n ↦ n) tend vers +∞`
-/

Exercice-lemme majoree_segment
  "12.07 Toute fonction continue sur un segment y est majorée."
  Données : {f : ℝ → ℝ} {a b : ℝ}
  Hypothèses : (hf : ∀ x ∈ [a, b], f est continue en x)
  Conclusion : ∃ M, ∀ x ∈ [a, b], f x ≤ M
Démonstration :
  Supposons par l'absurde H : ∀ M, ∃ x ∈ [a, b], M < f x
  Fait F : ∀ n : ℕ, ∃ x ∈ [a, b], f x > n car
    Soit n
    On conclut par hypothèse
  Comme ∀ n : ℕ, ∃ x ∈ [a, b], f x > n on choisit u : ℕ → ℝ
    tel que hu : ∀ n, u n ∈ [a, b] et hu' : ∀ n, f (u n) > n
  Par bolzano_weierstrass en utilisant que ∀ (n : ℕ), u n ∈ [a, b] on obtient
      (c : ℝ) (c_dans : c ∈ [a, b])
      (φ : ℕ → ℕ) (φ_extr : φ est une extraction) (lim_u_φ : u ∘ φ tend vers c)
  sorry
QED

/-
L’exercice suivant est une pause élémentaire. Il servira à déduire la version
minorée de l’énoncé précédent.
-/

Exercice-lemme continue_opposee
  "12.08 Si f est continue en x₀ alors -f est aussi continue en x₀"
  Données : {f : ℝ → ℝ} {x₀ : ℝ}
  Hypothèses : (h : f est continue en x₀)
  Conclusion : (fct x ↦ -f x) est continue en x₀
Démonstration :
  sorry
QED

/-
Voici maintenant la version minoration promise. Elle se démontre en combinant
simplement les deux exercices précédants.
-/
Exercice-lemme minoree_segment
  "12.9 Toute fonction continue sur un segment y est minorée."
  Données : {f : ℝ → ℝ} {a b : ℝ}
  Hypothèses :  (hf : ∀ x ∈ [a, b], f est continue en x)
  Conclusion : ∃ m, ∀ x ∈ [a, b], m ≤ f x
Démonstration :
  Fait clef : ∃ M, ∀ x ∈ [a, b], -f x ≤ M car
    sorry
  sorry
QED

/-
Nous avons démontré dans la feuille 8 qu'une suite a au plus une limite :

 `(u tend vers l ∧ u tend vers l') ⇒ l = l'`

et démontré dans la feuille 9 que si u tend vers l alors toutes ses suites
extraites tendent vers l :

  `(u tend vers l) ∧ (hφ : extraction φ) ⇒ u ∘ φ tend vers l`

On admet une version du théorème de la borne supérieure (qu'on ne peut pas
démontrer sans construire les nombres réels ou admettre un autre théorème
aussi fort) :

`∀ a b : ℝ, ∀ A : Set ℝ, (∃ x, x ∈ A) ∧ (h : A ⊆ [a, b]) ⇒
   ∃ x ∈ [a, b], x est borne sup de A`

Dans l'exercice suivant, il peut être utile de démontrer une inclusion
entre ensembles A et B de nombres réels.
Par définition, `A ⊆ B` signifie : `∀ x, x ∈ A ⇒ x ∈ B`.
On peut donc commencer la démonstration de A ⊆ B par « Soit x ∈ A »
qui fait apparaître « x : ℝ » et « x_mem : x ∈ A  » dans le contexte
puis démontrer x ∈ B.

On remarquera aussi l'utilisation de la notation
  {x | P x}
qui désigne l'ensemble des x vérifiant le prédicat P.
Par exemple, la définition du segment [a, b] est :
`[a, b] = { x | a ≤ x ∧ x ≤ b }`

Ainsi l'énoncé `y ∈ { x | P x}` signifie `P y`, par définition.

On utilisera aussi les résultats des exercices précédants :
Toute fonction continue sur un segment y est majorée et minorée, et la
continuité implique la continuité séquentielle.
-/

Exercice "12.10 Toute fonction continue sur un segment non vide y admet un maximum."
  Données : {a b : ℝ} {f : ℝ → ℝ}
  Hypothèses : (hab : a ≤ b) (hf : ∀ x ∈ [a, b], f est continue en x)
  Conclusion : ∃ x₀ ∈ [a, b], ∀ x ∈ [a, b], f x ≤ f x₀
Démonstration :
  Comme ∀ x ∈ [a, b], f est continue en x on obtient m
     tel que hm : ∀ x ∈ [a, b], m ≤ f x
  Comme ∀ x ∈ [a, b], f est continue en x on obtient M
     tel que hM : ∀ x ∈ [a, b], f x ≤ M
  Posons A := {y | ∃ x ∈ [a, b], y = f x} -- A est l'image de [a, b] par f
  Fait etape1 : ∃ y₀ ∈ [m, M], y₀ est borne sup de A car
    sorry
  Comme ∃ y₀ ∈ [m, M], y₀ est borne sup de A on obtient y₀
    tel que y_dans : y₀ ∈ [m, M] et y_sup : y₀ est borne sup de A
  Comme y₀ est borne sup de A on obtient y_maj : y₀ majore A
  Comme y₀ est borne sup de A on obtient u : ℕ → ℝ tel que
    lim_u : u tend vers y₀ et u_dans : ∀ n, u n ∈ A
  Comme ∀ n, u n ∈ A on choisit v : ℕ → ℝ tel que
    v_dans : ∀ n, v n ∈ [a, b] et hufv : ∀ n, u n = f (v n)
  Comme ∀ n, u n = f (v n) on obtient hu_eq_comp : u = f ∘ v
  sorry
QED

/-
Et maintenant le boss final... le théorème des valeurs intermédiaires

On utilisera le théorème des gendarmes (revoir la solution de l’exercise 12.02
pour se souvenir comment appliquer ce théorème).

On pourra utiliser l’énoncé évident suivant :
`∀ a b x : ℝ, (x ∈ [a, b] ∧ x ≠ b) ⇒ x < b`

et on utilisera de nouveau la version du théorème de la borne supérieure
`(∃ x, x ∈ A ∧ A ⊆ [a, b]) ⇒ ∃ x ∈ [a, b], x est borne sup de A`

ainsi que lemmes mentionés plus haut concernant la suite
`(suite n ↦ 1/(n+1))`, les passages à la limite dans les inégalités et la
continuité séquentielle des fonctions continues.
-/

Exercice "12.11 Le théorème des valeurs intermédiaires"
  Données : (f : ℝ → ℝ)
  Hypothèses : (hf : ∀ x, f est continue en x) (h₀ : f 0 < 0) (h₁ : f 1 > 0)
  Conclusion : ∃ x₀ ∈ [0, 1], f x₀ = 0
Démonstration :
  Posons A := { x | x ∈ [0, 1] ∧ f x < 0}
  Fait ex_x₀ : ∃ x₀ ∈ [0, 1], x₀ est borne sup de A car
    sorry
  Comme ∃ x₀ ∈ [0, 1], x₀ est borne sup de A on obtient x₀ tel que
    x₀_dans : x₀ ∈ [0, 1] et x₀_sup : x₀ est borne sup de A
  Montrons que x₀ convient
  Comme x₀ ∈ [0, 1] il suffit de montrer que f x₀ = 0
  Fait fx₀_neg : f x₀ ≤ 0 car
    sorry
  Fait x₀_1: x₀ < 1 car
    sorry
  Comme f x₀ ≤ 0 il suffit de montrer que f x₀ ≥ 0
  Fait dans' : ∃ N : ℕ, ∀ n ≥ N, x₀ + 1/(n+1) ∈ [0, 1] car
    Fait dans'' : ∃ N : ℕ, ∀ n ≥ N, 1/(n+1) ≤ 1 - x₀ car
      sorry
    sorry
  Comme ∃ N : ℕ, ∀ n ≥ N, x₀ + 1 / (n + 1) ∈ [0, 1]
    on obtient N : ℕ tel que hN : ∀ n ≥ N, x₀ + 1 / (n + 1) ∈ [0, 1]
  Fait pas_dans : ∀ n : ℕ, x₀ + 1/(n+1) ∉ A car
  -- Par définition, x ∉ A signifie « non (x ∈ A) ».
    sorry
  sorry
QED

