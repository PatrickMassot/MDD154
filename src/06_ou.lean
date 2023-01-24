import lib.m154


/-
# Disjonctions

Ce fichier est consacré au connecteur logique de disjonction, noté simplement « ou » 
sur papier et `∨` dans Lean ainsi que dans les livres de logique pure (attention
ce symbole n'est pas la lettre v). 

Pour *démontrer* un but de la forme `P ∨ Q`, on utilise 
`Montrons que P` et on démontre P ou `Montrons que Q` et
on démontre Q (il faut donc faire un choix stratégique).
-/

example : 2^3 = 3 ∨ 2^3 = 8 :=
begin
  Montrons que 2^3 = 8,
  On calcule,
end

example : 1 + 1 = 2 ∨ 1 + 3 = 17 :=
begin
  sorry
end


/-
Pour *utiliser* une hypothèse de la forme `hyp : P ∨ Q`
lors de la démonstration d'un but `R`, on tape
`On discute en utilisant hyp,`
(ou bien `On discute en utilisant (hyp : P ∨ Q),` pour plus de clarté)
qui crée deux branches dans la démonstration :
une branche où il faut démontrer `P → R`
et l'autre où il faut démontrer `Q → R`.
-/

example {a : ℝ} (h : a = 2 ∨ a = -2) : a^2 = 4 :=
begin
  On discute en utilisant h,
  Supposons ha : a = 2,
    calc 
      a^2 = 2^2 : by On réécrit via ha
      ... = 4   : by On calcule,
  Supposons ha : a = -2,
    calc 
      a^2 = (-2)^2 : by On réécrit via ha
      ... = 4   : by On calcule,
end

example {a : ℝ} (h : a = 2 ∨ a = -3) : a^2 + a = 6 :=
begin
  sorry
end


/-
Voyons maintenant des énoncés qui successivement utilisent et démontrent
une disjonction. L'utilisation d'une disjonction crée un embranchement 
dans la démonstration et la décision stratégique pour démontrer la disjonction
but dépend de la branche courante.

Dans l'exemple suivant, on utilise aussi
la commande `On combine` suivie d'une liste d'hypothèses,
qui cherche à démontrer une égalité ou une inégalité 
par combinaison linéaire de ces hypothèses. 
Si la liste ne consiste qu'en une seule hypothèse,
il est plus naturel d'utiliser `On conclut par`.
Cette commande permet aussi de déduire `a ≤ b` de `a < b`
ou d'autres trivialités de ce genre.

Enfin on utilise le lemme
`mul_eq_zero : a*b = 0 ↔ a = 0 ∨ b = 0`
qui servira aussi dans l'exercice suivant.
-/

example (a b : ℝ) : a = a*b → a = 0 ∨ b = 1 :=
begin
  Supposons hyp : a = a*b,
  Fait H : a*(1 - b) = 0,
    calc a*(1 - b) = a - a*b : by On calcule
               ... = 0       : by On conclut par hyp,
  On réécrit via mul_eq_zero dans H qui devient a = 0 ∨ 1 - b = 0,
  On discute en utilisant (H : a = 0 ∨ 1 - b = 0),
    Supposons H : a = 0,
    Montrons que a = 0,
    On conclut par H,
  Supposons H : 1 - b = 0,
  Montrons que b = 1,
  On conclut par H,
end

example (x y : ℝ) : x^2 = y^2 → x = y ∨ x = -y :=
begin
  sorry
end

/-
On va maintenant combiner le quantificateur universel
et la disjonction dans deux exercices plus intéressants.

On rappelle la définition de fonction croissante :
-/

def croissante (f : ℝ → ℝ) := ∀ x₁, (∀ x₂, x₁ ≤ x₂ → f x₁ ≤ f x₂)

/-
Dans l'exercice suivant, on pourra utiliser le lemme
`eq_or_lt_of_le : x ≤ y → x = y ∨ x < y`
-/
example (f : ℝ → ℝ) : croissante f ↔ ∀ x y, x < y → f x ≤ f y :=
begin
  sorry
end

/-
Dans l'exercice suivant, on pourra utiliser le lemme
`le_total x y : x ≤ y ∨ y ≤ x`

Cet exercice nécessite de réfléchir un peu plus que les
précédents, l'énoncé n'étant pas complètement évident.
-/
example (f : ℝ → ℝ) (h : croissante f) (h' : ∀ x, f (f x) = x) : ∀ x, f x = x :=
begin
  sorry
end

