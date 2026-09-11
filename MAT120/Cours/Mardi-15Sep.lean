import Verbose.French.ExampleLib
import MAT120.src.lois_logique

open Verbose.French
open Verbose.Named

/- Plan de la séance
- Syntax de base (∨ ∧ ¬ → ↔)
- Les ensembles de nombres, ℕ ℝ ℚ ℤ ≠ = etc
- La syntaxe d'un exercice
- LEAN infoview
- Les quantificateurs ∃ ∀ (syntax)
- `sorry` — la preuve par excuse
- Comment Lean place ses parenthèses

-/

/- LEAN est un un **assistant de preuve par ordinateur**, cette à dire, il permettre à
l'usager de savoir si une **propostion** est vraie. Dans LEAN, il y a des differents **types** d'objets, dont le plus important est le type Prop : -/

example (P : Prop) : Prop := P -- P est une proposition : un énoncé, ni vrai ni faux pour l'instant. On dit que P est un **terme** de `Prop`

/- Comment on l'appris, une proposition peut avoir deux valeurs de verité: Vrai ou Faux -/

example (P : Prop) (hP : P) : P := hP -- Ici, hp est un **terme** de P, ce qui pour LEAN veut dire que hp est un preuve que P est vraie

/- Dans les deux exemples precedents, on doit dire à LEAN qui sont P et hp. Ceci est déclaré entre `example` et `:`.

Apres `:`, vient la *demande*: dans le premier exemple on demande à LEAN un exemple de proposition, et on lui donne (`:=`) P. Dans le deuxieme exemple, on lui demande une preuve de P, et on lui donne (`:=`) hP. -/

-- Quelle est la signification de l'exemple suivant?

example (P : Prop) (nhP : ¬ P) : ¬ P := nhP

/- 1. Syntaxe de base des connecteurs

   Chaque symbole se tape avec une abréviation commençant par `\` :
     ∧  « et »          \and
     ∨  « ou »          \or
     ¬  « non »         \not
     →  « implique »    \to   (ou \imp)
     ↔  « équivaut à »  \iff
-/

example (P Q : Prop) : Prop := P ∧ Q
example (P Q : Prop) : Prop := P ∨ Q
example (P : Prop)   : Prop := ¬ P
example (P Q : Prop) : Prop := P → Q
example (P Q : Prop) : Prop := P ↔ Q


/- 2. Les ensembles de nombres

     ℕ  entiers naturels    \N
     ℤ  entiers relatifs    \Z
     ℚ  nombres rationnels   \Q
     ℝ  nombres réels        \R

   Égalité `=` ; différence `≠` (se tape \ne).
-/

example : ℕ := 42
example : ℤ := -7
example : ℝ := 3.5

example : (2 : ℕ) = 2 := by rfl -- Traduction:
example : (2 : ℝ) ≠ 3 := by norm_num -- Traduction:
#check (2 : ℝ)   -- on précise le type entre parenthèses

/- Dans les exemples précedents, `rfl` et `norm_num` sont des exemples de **techniques** de preuve.

D'après votre cours, quels exemples de techniques de preuve connaissez-vous?
R :=
-/

/- 3. La syntaxe d'un exercice avec VerboseLEAN

     Exemple "un titre"
       Données :    les objets : (P Q : Prop), (n : ℕ), ...
       Hypothèses : ce que l'on suppose : (h : P → Q) (hP : P)
       Conclusion : ce que l'on doit démontrer
     Démonstration :
       ... les étapes ...
     QED

   La section Hypothèses peut être vide. `QED` marque la fin.

-/

Exemple "Une implication évidente"
  Données : (P : Prop)
  Hypothèses :
  Conclusion : P → P
Démonstration :
  Supposons hP : P
  On conclut par hP
QED

Exemple "Exemple d'une preuve avec hypothèses"
  Données : (P Q : Prop) -- Traduction :
  Hypothèses : (h : P → Q) (hP : P) -- Traduction :
  Conclusion : Q
Démonstration :
  Par h il suffit de montrer que P -- Exemple de tactique, comparer avec l'excercise 1.23 b)
  On conclut par hP
QED

Exemple "Une autre façon de pruver une implication et de l'utiliser"
  Données : (P Q R: Prop) -- Traduction :
  Hypothèses : (h : R → P) (k : P → Q)
  Conclusion : R → Q
Démonstration :
  Supposons hR : R
  Par h appliqué à hR on obtient (hp : P) -- Ceci est une autre façon de rédiger la technique de preuve de l'implicaiton.
  On conclut par k appliqué à hp
QED

/- 4. Le panneau « Lean Infoview »

   En plaçant le curseur dans une preuve, le panneau de droite montre :
     - les objets et hypothèses disponibles (le contexte),
     - après `⊢`, le but : ce qu'il reste à démontrer.
   Le but change à chaque étape ; « No goals » = preuve finie.

   Soulignement rouge = erreur ; jaune = avertissement (souvent `sorry`).
-/

Exemple "Observer l'infoview"
  Données : (P Q : Prop)
  Hypothèses : (hP : P) (hQ : Q)
  Conclusion : P ∧ Q
Démonstration :
  Montrons d'abord que P
  On conclut par hP
  Montrons maintenant que Q
  On conclut par hQ
QED

/- 5. `sorry` — la preuve par excuse

   `sorry` dit à Lean « fais-moi confiance » : la preuve est acceptée mais
   Lean affiche un avertissement jaune. Ce n'est pas une vraie preuve.
-/

Exemple "Preuve à compléter"
  Données : (P Q : Prop)
  Hypothèses : (h : P → Q) (hP : P)
  Conclusion : Q
Démonstration :
  sorry
QED

/- 6. Les quantificateurs

     ∀  « pour tout »   \forall
     ∃  « il existe »   \exists

   Syntaxe :  ∀ x : ℕ, ...    ∃ x : ℕ, ...
   La virgule sépare la variable de l'énoncé.
-/

example : ∀ n : ℕ, n = n := by
  Soit n : ℕ
  On calcule

example : ∃ n : ℕ, n = 3 := by
  Montrons que 3 convient
  On calcule

example : ∀ x : ℕ, ∃ y : ℕ, x ≤ y := by
  Soit x : ℕ
  Montrons que x convient
  On calcule

/-Excercice: Traduction de la Proposition 2.4 du cours -/

Exemple "Proposition 2.4"
  Données: (n : ℤ) (n_est_pair = (∃ k : ℤ, n = 2*k) : Prop)
  Hypothèses:
  Conclusion: (∃ k : ℤ, n = 2*k) → (∃ k' :ℤ, n^2 = 2*k')
Démonstration:
 sorry
QED


/- 7. Comment Lean place ses parenthèses

   Sans parenthèses, Lean les ajoute selon des priorités fixes,
   du plus « collant » au moins « collant » :
     ¬   puis   ∧   puis   ∨   puis   →   puis   ↔
   `→` s'associe à droite ; un quantificateur s'étend le plus loin possible.

   Ci-dessous les deux membres sont le même énoncé pour Lean (`Iff.rfl` est la tecnique equivalente à faire des calculs propositionels) :
   seules les parenthèses changent.
-/

example (P Q : Prop)     : (¬ P ∧ Q)         ↔ ((¬ P) ∧ Q)            := Iff.rfl
example (P Q R : Prop)   : (P ∨ Q ∧ R)       ↔ (P ∨ (Q ∧ R))          := Iff.rfl
example (P Q R : Prop)   : (P ∧ Q → R)       ↔ ((P ∧ Q) → R)          := Iff.rfl
example (P Q R : Prop)   : (P → Q → R)       ↔ (P → (Q → R))          := Iff.rfl
example (P Q R : Prop)   : (P → Q ↔ R)       ↔ ((P → Q) ↔ R)          := Iff.rfl
example (P Q : ℕ → Prop) : (∀ x, P x ∧ Q x)  ↔ (∀ x, (P x ∧ Q x))     := Iff.rfl

/- Excercices -/

/- Démontrer en utilisant seulement les lois de LP-1 à LP-13-/
Exemple "Laboratoire 4 1)"
  Données : (A B : Prop)
  Hypothèses :
  Conclusion : (A ∨ (A ∧ B)) ↔ A
Démonstration :
On réécrit via LP_12
On réécrit via LP_6
On réécrit via LP_11
On réécrit via LP_5
On réécrit via LP_14
QED

/- Ecrire sa contraposée-/

Exemple "Contraposée"
Données : (n : ℕ)
Hypothèses :
Conclusion : (∀ k : ℕ, n ≠ k*2) → (∀ k' : ℕ, n ≠ k'*4)
Démonstration :
  On contrapose
  sorry
QED

/- Things like this to see in the second week-/
Exemple "Exemple 1.6 des notes de cours"
 Données : (n : ℕ)
 Hypothèses : (h : (∃ k : ℕ, n = k*4)) /- n est divisible par 4 -/
 Conclusion : (∃ k' : ℕ, n = k'*2) /- n est pair -/
Démonstration :
 Par h on obtient k tel que (hk : n = k*4) /-Attention : LEAN ne sait pas que l*4 = 4*l-/
 Montrons que k*2 convient /- k*2 = k'-/
 Calc n = k*4 par hk
      _ = k*2*2 par calcul /- Please write in your code what you use? -/
QED

/-
Note: Le but de ce cours est de vous presenter LEAN comme un outil d'apprentissage de la logique mathématique. LEAN es aussi utilisée de façon professionel par des mathematiciens et infomaticiens. Dans ce cours on utilise VerboseLEAN, une version de LEAN qu'utilise le langage naturel (proche de ce que vous écrirez dans vos notes par exemple). Par contre, la syntax "normale" de LEAN resemble plus à un langage de programation.
-/
