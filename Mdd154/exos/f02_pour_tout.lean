import Mdd154.Lib
setup_env

/-
# Feuille 2 : Quantificateur universel
-/

/-
On rappelle que `f est paire` signifie `∀ x, f (-x) = f x` et
`f est impaire` signifie `∀ x, f (-x) = -f x`.

Dans l’exemple suivant, on démontre un énoncé de la forme `∀ x, P x` en utilisant
la commande `Soit`.
-/

Exemple "La fonction qui envoie x sur x² est paire."
  Données :
  Hypothèses :
  Conclusion : (fct x ↦ x^2) est paire
Démonstration :
  Soit x : ℝ
  Montrons que (-x)^2 = x^2
  On calcule
QED

Exercice "02.1 La fonction qui envoie `x` sur `x³` est impaire."
  Données :
  Hypothèses :
  Conclusion : (fct x ↦ x^3) est impaire
Démonstration :
  sorry
QED

/-
Dans les exemples suivants, on utilise un énoncé débutant par un quantificateur universel
au moyen des commandes `Comme … on conclut …` ou `Comme … on obtient …` selon qu’on obtient
directement la conclusion voulue ou que l’on souhaite obtenir un fait intermédiaire.
-/

Exemple "Spécialisation d’une hypothèse de parité pour conclure."
  Données : (f : ℝ → ℝ)
  Hypothèses : (hf : f est paire)
  Conclusion : f (-5) = f 5
Démonstration :
  Comme f est paire on conclut que f (-5) = f 5
QED

Exemple "Spécialisation d’une hypothèse de parité en créant un fait intermédiaire."
  Données : (f g : ℝ → ℝ)
  Hypothèses : (hf : f est paire)
  Conclusion : g (f (-5)) = g (f 5)
Démonstration :
  Comme f est paire on obtient hf5 : f (-5) = f 5
  Comme f (-5) = f 5 on conclut que g (f (-5)) = g (f 5)
QED

Exercice "02.2 Spécialisation d’une hypothèse d’imparité."
  Données : (f : ℝ → ℝ)
  Hypothèses : (hf : f est impaire)
  Conclusion : f (-3) = -f 3
Démonstration :
  sorry
QED

/-
Voyons maintenant un exemple qui démontre un énoncé quantifié en utilisant
deux hypothèses quantifiées.
Dans cet exemple, on nomme `x₀` le nombre réel introduit par la
commande `Soit` pour insister sur le fait qu’il est fixé et bien voir
qu’après la ligne `Comme f est paire on obtient hfx₀ : f (-x₀) = f x₀`, la nouvelle
hypothèse `hfx₀` ne porte que sur ce seul nombre.

On notera aussi que la justification `par calcul`, destinée aux étapes
n’utilisant pas d’hypothèse, s’occupe de la définition
de l’addition de fonctions. De même, dans des exercices suivants, elle s’occupera
de celle de la composition de fonctions.
-/

Exemple "Si f et g sont paires alors leur somme l’est aussi."
  Données : (f g : ℝ → ℝ)
  Hypothèses : (hf : f est paire) (hg : g est paire)
  Conclusion : (f + g) est paire
Démonstration :
  Montrons que ∀ x, (f + g) (-x) = (f + g) x
  Soit x₀ : ℝ
  Comme f est paire on obtient hf₀ : f (-x₀) = f x₀
  Comme g est paire on obtient hg₀ : g (-x₀) = g x₀
  Calc
    (f + g) (-x₀) = f (-x₀) + g (-x₀) par calcul
    _             = f x₀ + g (-x₀)    puisque f (-x₀) = f x₀
    _             = f x₀ + g x₀       puisque g (-x₀) = g x₀
    _             = (f + g) x₀        par calcul
QED

/-
Dans la démonstration précédente, la ligne commençant par "Montrons que"
est purement psychologique, Lean n’en a pas besoin du tout.

Enfin Lean n’a pas vraiment besoin qu’on lui dise à quel réel appliquer
les hypothèses de parité, il lui suffit de chercher dans l’égalité à justifier
donc les lignes de spécialisation sont inutiles.

On peut donc aussi utiliser la version ci-dessous.
-/

Exemple "Si f et g sont paires alors leur somme l’est aussi, avec une démonstration concise."
  Données : (f g : ℝ → ℝ)
  Hypothèses :(hf : f est paire) (hg : g est paire)
  Conclusion : (f + g) est paire
Démonstration :
  Soit x₀
  Calc
    (f + g) (-x₀) = f (-x₀) + g (-x₀) par calcul
    _             = f x₀ + g (-x₀)    puisque f est paire
    _             = f x₀ + g x₀       puisque g est paire
    _             = (f + g) x₀        par calcul
QED

Exercice "02.3 Précomposer par une fonction paire donne une fonction paire."
  Données : (f g : ℝ → ℝ)
  Hypothèses : (hf : f est paire)
  Conclusion : (g ∘ f) est paire
Démonstration :
  sorry
QED

Exercice "02.4 La composée de deux fonctions impaires est impaire."
  Données : (f g : ℝ → ℝ)
  Hypothèses : (hf : f est impaire) (hg : g est impaire)
  Conclusion : (g ∘ f) est impaire
Démonstration :
  sorry
QED

