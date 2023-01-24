import lib.m154

/-
# Un apercu du cours de Logique et démonstations assistées par ordinateur

Ce fichier ne contient pas d'exercice, son but est de montrer à quoi
va ressembler une démonstration expliquée à l'ordinateur au milieu du semestre.
Le but de ce cours est de parvenir à concevoir et rédiger ce genre de
démonstration sur papier.

La syntaxe et les différentes commandes seront expliquées au fur et à mesure.
Pour l'instant, il suffit de lire les définitions, l'énoncé et la démonstration
ci-dessous et de ce convaincre que cela rappelle des souvenirs du cours d'analyse
du premier semestre.

Ce fichier est prévu pour être ouvert dans l'éditeur Visual Studio Code (ou VSCodium).
La partie droite de l'écran doit afficher une zone intitulée « Lean Infoview ».
Si ce n'est pas le cas, la combinaison de touche Ctrl-Maj-Entrée 
(ou Cmd-Maj-Entrée sur un Mac) doit la faire apparaître. Si cette zone
Infoview se retrouve accidentellement dans un onglet difficile d'accès, le plus 
simple est de fermer l'onglet et de rouvrir la zone par Ctrl-Maj-Entrée.

Lorsque le curseur se trouve dans la démonstration, la zone « Lean Infoview »
affiche les objets et hypothèses intervenant à ce stade de la démonstration,
ainsi que le ou les buts de la démonstration.
-/

-- Définition de « f est continue en x₀ »
-- Lean n'a pas besoin de parenthèse dans f(x)
def continue_en (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε

-- Une suite u est une fonction de ℕ dans ℝ
-- Définition de « u tend vers l »
def limite_suite (u : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

-- Soit f une fonction, u une suite de réels et x₀ un réel.
-- Si f est continue en x₀ et si la suite u tend vers x₀ alors la suite f ∘ u,
-- qui envoie n sur f (u n), tend vers f x₀
example (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ) 
  (hf : continue_en f x₀) (hu : limite_suite u x₀) :
  limite_suite (f ∘ u) (f x₀) :=
begin
  Montrons que ∀ ε > 0, ∃ N, ∀ n ≥ N, |(f ∘ u) n - f x₀| ≤ ε,
  Soit ε > 0,
  Par hf appliqué à [ε, ε_pos] on obtient δ : ℝ tel que 
    (δ_pos : δ > 0) (hδf : ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε),
  Par hu appliqué à [δ, δ_pos] on obtient N : ℕ tel que
    (hNu : ∀ n ≥ N, |u n - x₀| ≤ δ),
  Montrons que N convient : ∀ n ≥ N, |(f ∘ u) n - f x₀| ≤ ε,
  Soit n ≥ N,
  Montrons que |(f ∘ u) n - f x₀| ≤ ε,
  Par hδf il suffit de montrer que |u n - x₀| ≤ δ,
  On conclut par hNu appliqué à [n, n_ge],
end

