import Verbose.French.ExampleLib

open Verbose.French
open Verbose.Named

/-
  Aide-mémoire : tactiques VerboseLean (français)

  Un exemple minimal par commande, pour les chapitres 2 à 4 du cours de Patrick Massot : https://www.imo.universite-paris-saclay.fr/~patrick.massot/mdd154/
    - Chapitre 2 : implications, équivalences, conjonctions, disjonctions
    - Chapitre 3 : prédicats et quantificateurs
    - Chapitre 4 : négations, absurde, contraposée
-/

/- ================= IMPLICATION (→) ================= -/

-- Prouver une implication : `Supposons`
Exemple "Prouver P → Q : Supposons"
 Données : (P Q : Prop)
 Hypothèses : (h : P → Q)
 Conclusion : P → Q
Démonstration :
 Supposons hP : P
 On conclut par h hP
QED

-- Utiliser une implication en avant : `on conclut par ... appliqué à ...`
Exemple "Utiliser P → Q en avant"
 Données : (P Q : Prop)
 Hypothèses : (h : P → Q) (hP : P)
 Conclusion : Q
Démonstration :
 On conclut par h appliqué à hP
QED

-- Utiliser une implication en arrière : `il suffit de montrer que`
Exemple "Utiliser P → Q en arrière"
 Données : (P Q : Prop)
 Hypothèses : (h : P → Q) (hP : P)
 Conclusion : Q
Démonstration :
 Par h il suffit de montrer que P
 On conclut par hP
QED

/- ================= CONJONCTION (∧) ================= -/

-- Prouver une conjonction : `Montrons d'abord que ... / Montrons maintenant que ...`
Exemple "Prouver P ∧ Q"
 Données : (P Q : Prop)
 Hypothèses : (hP : P) (hQ : Q)
 Conclusion : P ∧ Q
Démonstration :
 Montrons d'abord que P
 On conclut par hP
 Montrons maintenant que Q
 On conclut par hQ
QED

-- Utiliser une conjonction : `Par ... on obtient (...) (...)`
Exemple "Utiliser P ∧ Q"
 Données : (P Q : Prop)
 Hypothèses : (h : P ∧ Q)
 Conclusion : Q ∧ P
Démonstration :
 Par h on obtient (hP : P) (hQ : Q)
 Montrons d'abord que Q
 On conclut par hQ
 Montrons maintenant que P
 On conclut par hP
QED

/- ================= DISJONCTION (∨) ================= -/

-- Prouver une disjonction : choisir la branche avec `Montrons que`
Exemple "Prouver P ∨ Q en choisissant la branche Q"
 Données : (P Q : Prop)
 Hypothèses : (hQ : Q)
 Conclusion : P ∨ Q
Démonstration :
 Montrons que Q
 On conclut par hQ
QED

-- Utiliser une disjonction : `On discute en utilisant`
Exemple "Utiliser P ∨ Q"
 Données : (P Q R : Prop)
 Hypothèses : (h : P ∨ Q) (hPR : P → R) (hQR : Q → R)
 Conclusion : R
Démonstration :
 On discute en utilisant h
 Supposons hP : P
 On conclut par hPR hP
 Supposons hQ : Q
 On conclut par hQR hQ
QED

-- Tiers exclu : `On discute selon que ...` (scinde en deux cas P et ¬P)
Exemple "Tiers exclu : on discute selon que P"
 Données : (P R : Prop)
 Hypothèses : (hP : P → R) (hnP : ¬P → R)
 Conclusion : R
Démonstration :
 On discute selon que P
 Supposons hP' : P
 On conclut par hP hP'
 Supposons hnP' : ¬P
 On conclut par hnP hnP'
QED

/- ================= ÉQUIVALENCE (↔) ================= -/

-- Prouver une équivalence : `Montrons d'abord que ... / Montrons maintenant que ...`
Exemple "Prouver P ↔ Q"
 Données : (P Q : Prop)
 Hypothèses : (hPQ : P → Q) (hQP : Q → P)
 Conclusion : P ↔ Q
Démonstration :
 Montrons d'abord que P → Q
 On conclut par hPQ
 Montrons maintenant que Q → P
 On conclut par hQP
QED

-- Utiliser une équivalence : `Par ... on obtient (... → ...) (... → ...)`
Exemple "Utiliser P ↔ Q"
 Données : (P Q : Prop)
 Hypothèses : (h : P ↔ Q) (hP : P)
 Conclusion : Q
Démonstration :
 Par h on obtient (hPQ : P → Q) (hQP : Q → P)
 On conclut par hPQ hP
QED

/- ================= NÉGATION, ABSURDE, CONTRAPOSÉE ================= -/

-- Raisonnement par l'absurde : `Supposons par l'absurde`
Exemple "Raisonnement par l'absurde : double négation"
 Données : (P : Prop)
 Hypothèses : (hnnP : ¬¬P)
 Conclusion : P
Démonstration :
 Supposons par l'absurde hnP : ¬P
 On conclut par hnnP hnP
QED

-- Contraposée : `On contrapose`
Exemple "Contraposée"
 Données : (P Q : Prop)
 Hypothèses : (h : ¬Q → ¬P)
 Conclusion : P → Q
Démonstration :
 On contrapose
 On conclut par h
QED

/- ================= QUANTIFICATEURS ================= -/

-- Prouver un ∀ : `Soit`
Exemple "∀ : Soit"
 Données : (P : ℕ → Prop)
 Hypothèses : (h : ∀ n : ℕ, P n)
 Conclusion : ∀ n : ℕ, P n
Démonstration :
 Soit n : ℕ
 On conclut par h n
QED

-- Utiliser un ∀ : spécialiser avec `On applique ... à ...`
Exemple "∀ : spécialiser avec On applique ... à ..."
 Données : (P : ℕ → Prop) (n₀ : ℕ)
 Hypothèses : (h : ∀ n : ℕ, P n)
 Conclusion : P n₀
Démonstration :
 On applique h à n₀
 On conclut par h
QED

-- Utiliser un ∃ : extraire un témoin avec `on obtient ... tel que`
Exemple "∃ : extraire un témoin"
 Données : (n : ℕ)
 Hypothèses : (h : ∃ k : ℕ, n = k*4)
 Conclusion : ∃ k' : ℕ, n = k'*4
Démonstration :
 Par h on obtient (k : ℕ) tel que (hk : n = k*4)
 Montrons que k convient
 On conclut par hk
QED

-- ∀ et ∃ ensemble : exemple complet (divisible par 4 ⇒ divisible par 2)
Exemple "∀ et ∃ ensemble"
 Données : (n : ℕ)
 Hypothèses : (h : ∃ k : ℕ, n = k*4)
 Conclusion : ∃ k' : ℕ, n = k'*2
Démonstration :
 Par h on obtient (k : ℕ) tel que (hk : n = k*4)
 Montrons que k*2 convient
 Calc n = k*4    par hk
    _   = k*2*2  par calcul
QED
