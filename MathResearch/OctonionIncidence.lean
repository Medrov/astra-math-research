import MathResearch.AlbertObstruction
import MathResearch.ProbeLowerBound
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.List.Permutation
import Mathlib.Tactic

/-!
# Fixed-probe tomography of a relabelled octonion basis

A kernel-checked certificate connecting actual rational Cayley-Dickson
associators to two puncturings of the known 35-coordinate Fano-plane code.
The 10-probe certificate reconstructs all zero-associator incidence.
The 18-probe certificate has minimum distance at least three.
An information-counting theorem rules out any 8 fixed incidence probes.
These are concrete certificates, not a claim of historical novelty or optimality.
Orientations and basis signs are deliberately not reconstructed.
-/

namespace MathResearch.OctonionIncidence
open MathResearch.Albert
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 10000

abbrev Label := Fin 7

local instance : DecidableEq (Quaternion ℚ) := fun x y =>
  decidable_of_iff (x.re = y.re ∧ x.imI = y.imI ∧ x.imJ = y.imJ ∧ x.imK = y.imK)
    QuaternionAlgebra.ext_iff.symm

def basis : Label → Oct :=
  ![(⟨0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 1⟩, 0),
    (0, 1), (0, ⟨0, 1, 0, 0⟩), (0, ⟨0, 0, 1, 0⟩), (0, ⟨0, 0, 0, 1⟩)]

def associator (x y z : Oct) : Oct :=
  octMul (octMul x y) z - octMul x (octMul y z)

def binaryCondition (i j k : Label) : Prop :=
  i = j ∨ i = k ∨ j = k ∨ Nat.xor (i.val + 1) (Nat.xor (j.val + 1) (k.val + 1)) = 0

instance (i j k : Label) : Decidable (binaryCondition i j k) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

/-- All 343 ordered triples are evaluated in the actual octonion operations. -/
theorem basis_associator_zero_iff : ∀ i j k : Label,
    associator (basis i) (basis j) (basis k) = 0 ↔ binaryCondition i j k := by
  decide +kernel

def triples : Fin 35 → Label × Label × Label :=
  ![(0, 1, 2),
    (0, 1, 3),
    (0, 1, 4),
    (0, 1, 5),
    (0, 1, 6),
    (0, 2, 3),
    (0, 2, 4),
    (0, 2, 5),
    (0, 2, 6),
    (0, 3, 4),
    (0, 3, 5),
    (0, 3, 6),
    (0, 4, 5),
    (0, 4, 6),
    (0, 5, 6),
    (1, 2, 3),
    (1, 2, 4),
    (1, 2, 5),
    (1, 2, 6),
    (1, 3, 4),
    (1, 3, 5),
    (1, 3, 6),
    (1, 4, 5),
    (1, 4, 6),
    (1, 5, 6),
    (2, 3, 4),
    (2, 3, 5),
    (2, 3, 6),
    (2, 4, 5),
    (2, 4, 6),
    (2, 5, 6),
    (3, 4, 5),
    (3, 4, 6),
    (3, 5, 6),
    (4, 5, 6)]

def representatives : Fin 30 → Label → Label :=
  ![![0, 1, 2, 3, 4, 5, 6],
    ![0, 1, 2, 3, 4, 6, 5],
    ![0, 1, 2, 3, 5, 4, 6],
    ![0, 1, 2, 3, 6, 4, 5],
    ![0, 1, 2, 3, 5, 6, 4],
    ![0, 1, 2, 3, 6, 5, 4],
    ![0, 1, 3, 2, 4, 5, 6],
    ![0, 1, 3, 2, 4, 6, 5],
    ![0, 1, 3, 2, 5, 4, 6],
    ![0, 1, 3, 2, 6, 4, 5],
    ![0, 1, 3, 2, 5, 6, 4],
    ![0, 1, 3, 2, 6, 5, 4],
    ![0, 1, 3, 4, 2, 5, 6],
    ![0, 1, 3, 4, 2, 6, 5],
    ![0, 1, 3, 5, 2, 4, 6],
    ![0, 1, 3, 6, 2, 4, 5],
    ![0, 1, 3, 5, 2, 6, 4],
    ![0, 1, 3, 6, 2, 5, 4],
    ![0, 1, 3, 4, 5, 2, 6],
    ![0, 1, 3, 4, 6, 2, 5],
    ![0, 1, 3, 5, 4, 2, 6],
    ![0, 1, 3, 6, 4, 2, 5],
    ![0, 1, 3, 5, 6, 2, 4],
    ![0, 1, 3, 6, 5, 2, 4],
    ![0, 1, 3, 4, 5, 6, 2],
    ![0, 1, 3, 4, 6, 5, 2],
    ![0, 1, 3, 5, 4, 6, 2],
    ![0, 1, 3, 6, 4, 5, 2],
    ![0, 1, 3, 5, 6, 4, 2],
    ![0, 1, 3, 6, 5, 4, 2]]

def incidence (p : Label → Label) (t : Fin 35) : Bool :=
  decide (binaryCondition (p (triples t).1) (p (triples t).2.1) (p (triples t).2.2))

def actualResponse (p : Label → Label) (t : Fin 35) : Bool :=
  decide (associator (basis (p (triples t).1)) (basis (p (triples t).2.1))
    (basis (p (triples t).2.2)) = 0)

/-- This is a bridge for arbitrary relabelling maps, not just the catalogue. -/
theorem actualResponse_eq_incidence (p : Label → Label) (t : Fin 35) :
    actualResponse p t = incidence p t := by
  unfold actualResponse incidence
  simp only [basis_associator_zero_iff]

theorem representatives_bijective : ∀ i : Fin 30,
    Function.Bijective (representatives i) := by
  decide +kernel

def listMap (xs : List Label) (i : Label) : Label := (xs[i.val]?).getD 0

def allPermutationLists : List (List Label) := (List.finRange 7).permutations'

theorem listMap_ofFn (p : Equiv.Perm Label) : listMap (List.ofFn p) = p := by
  funext i
  simp only [listMap, List.getElem?_ofFn, dif_pos i.isLt, Option.getD_some]

theorem ofFn_mem_allPermutationLists (p : Equiv.Perm Label) :
    List.ofFn p ∈ allPermutationLists := by
  apply List.mem_permutations'.mpr
  rw [List.ofFn_eq_map]
  exact p.map_finRange_perm

def catalogueWords : List (List Bool) :=
  [[true, false, false, false, false, false, false, false, false, true, false, false, false, false, true, false, false, false, false, false, true, false, false, true, false, false, false, true, true, false, false, false, false, false, false],
    [true, false, false, false, false, false, false, false, false, true, false, false, false, false, true, false, false, false, false, false, false, true, true, false, false, false, true, false, false, true, false, false, false, false, false],
    [true, false, false, false, false, false, false, false, false, false, true, false, false, true, false, false, false, false, false, true, false, false, false, false, true, false, false, true, true, false, false, false, false, false, false],
    [true, false, false, false, false, false, false, false, false, false, true, false, false, true, false, false, false, false, false, false, false, true, true, false, false, true, false, false, false, false, true, false, false, false, false],
    [true, false, false, false, false, false, false, false, false, false, false, true, true, false, false, false, false, false, false, true, false, false, false, false, true, false, true, false, false, true, false, false, false, false, false],
    [true, false, false, false, false, false, false, false, false, false, false, true, true, false, false, false, false, false, false, false, true, false, false, true, false, true, false, false, false, false, true, false, false, false, false],
    [false, true, false, false, false, false, true, false, false, false, false, false, false, false, true, false, false, true, false, false, false, false, false, true, false, false, false, true, false, false, false, true, false, false, false],
    [false, true, false, false, false, false, true, false, false, false, false, false, false, false, true, false, false, false, true, false, false, false, true, false, false, false, true, false, false, false, false, false, true, false, false],
    [false, true, false, false, false, false, false, true, false, false, false, false, false, true, false, false, true, false, false, false, false, false, false, false, true, false, false, true, false, false, false, true, false, false, false],
    [false, true, false, false, false, false, false, true, false, false, false, false, false, true, false, false, false, false, true, false, false, false, true, false, false, true, false, false, false, false, false, false, false, true, false],
    [false, true, false, false, false, false, false, false, true, false, false, false, true, false, false, false, true, false, false, false, false, false, false, false, true, false, true, false, false, false, false, false, true, false, false],
    [false, true, false, false, false, false, false, false, true, false, false, false, true, false, false, false, false, true, false, false, false, false, false, true, false, true, false, false, false, false, false, false, false, true, false],
    [false, false, true, false, false, true, false, false, false, false, false, false, false, false, true, false, false, true, false, false, false, true, false, false, false, false, false, false, false, true, false, true, false, false, false],
    [false, false, true, false, false, true, false, false, false, false, false, false, false, false, true, false, false, false, true, false, true, false, false, false, false, false, false, false, true, false, false, false, true, false, false],
    [false, false, true, false, false, false, false, true, false, false, false, true, false, false, false, true, false, false, false, false, false, false, false, false, true, false, false, false, false, true, false, true, false, false, false],
    [false, false, true, false, false, false, false, true, false, false, false, true, false, false, false, false, false, false, true, false, true, false, false, false, false, true, false, false, false, false, false, false, false, false, true],
    [false, false, true, false, false, false, false, false, true, false, true, false, false, false, false, true, false, false, false, false, false, false, false, false, true, false, false, false, true, false, false, false, true, false, false],
    [false, false, true, false, false, false, false, false, true, false, true, false, false, false, false, false, false, true, false, false, false, true, false, false, false, true, false, false, false, false, false, false, false, false, true],
    [false, false, false, true, false, true, false, false, false, false, false, false, false, true, false, false, true, false, false, false, false, true, false, false, false, false, false, false, false, false, true, true, false, false, false],
    [false, false, false, true, false, true, false, false, false, false, false, false, false, true, false, false, false, false, true, true, false, false, false, false, false, false, false, false, true, false, false, false, false, true, false],
    [false, false, false, true, false, false, true, false, false, false, false, true, false, false, false, true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, true, true, false, false, false],
    [false, false, false, true, false, false, true, false, false, false, false, true, false, false, false, false, false, false, true, true, false, false, false, false, false, false, true, false, false, false, false, false, false, false, true],
    [false, false, false, true, false, false, false, false, true, true, false, false, false, false, false, true, false, false, false, false, false, false, false, true, false, false, false, false, true, false, false, false, false, true, false],
    [false, false, false, true, false, false, false, false, true, true, false, false, false, false, false, false, true, false, false, false, false, true, false, false, false, false, true, false, false, false, false, false, false, false, true],
    [false, false, false, false, true, true, false, false, false, false, false, false, true, false, false, false, true, false, false, false, true, false, false, false, false, false, false, false, false, false, true, false, true, false, false],
    [false, false, false, false, true, true, false, false, false, false, false, false, true, false, false, false, false, true, false, true, false, false, false, false, false, false, false, false, false, true, false, false, false, true, false],
    [false, false, false, false, true, false, true, false, false, false, true, false, false, false, false, true, false, false, false, false, false, false, true, false, false, false, false, false, false, false, true, false, true, false, false],
    [false, false, false, false, true, false, true, false, false, false, true, false, false, false, false, false, false, true, false, true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, true],
    [false, false, false, false, true, false, false, true, false, true, false, false, false, false, false, true, false, false, false, false, false, false, true, false, false, false, false, false, false, true, false, false, false, true, false],
    [false, false, false, false, true, false, false, true, false, true, false, false, false, false, false, false, true, false, false, false, true, false, false, false, false, false, false, true, false, false, false, false, false, false, true]]

theorem catalogueWords_eq : catalogueWords =
    (List.finRange 30).map (fun i => List.ofFn (incidence (representatives i))) := by
  decide +kernel

/-- Join two already checked sections without re-evaluating their finite certificates. -/
theorem catalogue_chunk_step {α : Type*} (xs : List α) (f : α → Bool) (n : Nat)
    (hchunk : ((xs.drop n).take 100).all f = true)
    (htail : (xs.drop (n + 100)).all f = true) :
    (xs.drop n).all f = true := by
  rw [← List.take_append_drop 100 (xs.drop n), List.all_append]
  rw [hchunk, List.drop_drop, htail]
  rfl

#print axioms catalogue_chunk_step

def cataloguePredicate (q : List Label) : Bool :=
  catalogueWords.contains (List.ofFn (incidence (listMap q)))

/- Each declaration has its own bounded kernel normalization. All sections,
including the final tail, are joined in catalogue_coverage below. -/
theorem catalogue_chunk_00 : ((allPermutationLists.drop 0).take 100).all cataloguePredicate = true := by
  decide +kernel

#print axioms catalogue_chunk_00

theorem catalogue_chunk_01 : ((allPermutationLists.drop 100).take 100).all cataloguePredicate = true := by
  decide +kernel

#print axioms catalogue_chunk_01

theorem catalogue_chunk_02 : ((allPermutationLists.drop 200).take 100).all cataloguePredicate = true := by
  decide +kernel

#print axioms catalogue_chunk_02

theorem catalogue_chunk_03 : ((allPermutationLists.drop 300).take 100).all cataloguePredicate = true := by
  decide +kernel

#print axioms catalogue_chunk_03

theorem catalogue_chunk_04 : ((allPermutationLists.drop 400).take 100).all cataloguePredicate = true := by
  decide +kernel

#print axioms catalogue_chunk_04

theorem catalogue_chunk_05 : ((allPermutationLists.drop 500).take 100).all cataloguePredicate = true := by
  decide +kernel

#print axioms catalogue_chunk_05

theorem catalogue_chunk_06 : ((allPermutationLists.drop 600).take 100).all cataloguePredicate = true := by
  decide +kernel

#print axioms catalogue_chunk_06

theorem catalogue_chunk_07 : ((allPermutationLists.drop 700).take 100).all cataloguePredicate = true := by
  decide +kernel

#print axioms catalogue_chunk_07

theorem catalogue_chunk_08 : ((allPermutationLists.drop 800).take 100).all cataloguePredicate = true := by
  decide +kernel

#print axioms catalogue_chunk_08

theorem catalogue_chunk_09 : ((allPermutationLists.drop 900).take 100).all cataloguePredicate = true := by
  decide +kernel

#print axioms catalogue_chunk_09

theorem catalogue_chunk_10 : ((allPermutationLists.drop 1000).take 100).all cataloguePredicate = true := by
  decide +kernel

#print axioms catalogue_chunk_10

theorem catalogue_chunk_11 : ((allPermutationLists.drop 1100).take 100).all cataloguePredicate = true := by
  decide +kernel

#print axioms catalogue_chunk_11

theorem catalogue_chunk_12 : ((allPermutationLists.drop 1200).take 100).all cataloguePredicate = true := by
  decide +kernel

#print axioms catalogue_chunk_12

theorem catalogue_chunk_13 : ((allPermutationLists.drop 1300).take 100).all cataloguePredicate = true := by
  decide +kernel

#print axioms catalogue_chunk_13

theorem catalogue_chunk_14 : ((allPermutationLists.drop 1400).take 100).all cataloguePredicate = true := by
  decide +kernel

#print axioms catalogue_chunk_14

theorem catalogue_chunk_15 : ((allPermutationLists.drop 1500).take 100).all cataloguePredicate = true := by
  decide +kernel

#print axioms catalogue_chunk_15

theorem catalogue_chunk_16 : ((allPermutationLists.drop 1600).take 100).all cataloguePredicate = true := by
  decide +kernel

#print axioms catalogue_chunk_16

theorem catalogue_chunk_17 : ((allPermutationLists.drop 1700).take 100).all cataloguePredicate = true := by
  decide +kernel

#print axioms catalogue_chunk_17

theorem catalogue_chunk_18 : ((allPermutationLists.drop 1800).take 100).all cataloguePredicate = true := by
  decide +kernel

#print axioms catalogue_chunk_18

theorem catalogue_chunk_19 : ((allPermutationLists.drop 1900).take 100).all cataloguePredicate = true := by
  decide +kernel

#print axioms catalogue_chunk_19

theorem catalogue_chunk_20 : ((allPermutationLists.drop 2000).take 100).all cataloguePredicate = true := by
  decide +kernel

#print axioms catalogue_chunk_20

theorem catalogue_chunk_21 : ((allPermutationLists.drop 2100).take 100).all cataloguePredicate = true := by
  decide +kernel

#print axioms catalogue_chunk_21

theorem catalogue_chunk_22 : ((allPermutationLists.drop 2200).take 100).all cataloguePredicate = true := by
  decide +kernel

#print axioms catalogue_chunk_22

theorem catalogue_chunk_23 : ((allPermutationLists.drop 2300).take 100).all cataloguePredicate = true := by
  decide +kernel

#print axioms catalogue_chunk_23

theorem catalogue_chunk_24 : ((allPermutationLists.drop 2400).take 100).all cataloguePredicate = true := by
  decide +kernel

#print axioms catalogue_chunk_24

theorem catalogue_chunk_25 : ((allPermutationLists.drop 2500).take 100).all cataloguePredicate = true := by
  decide +kernel

#print axioms catalogue_chunk_25

theorem catalogue_chunk_26 : ((allPermutationLists.drop 2600).take 100).all cataloguePredicate = true := by
  decide +kernel

#print axioms catalogue_chunk_26

theorem catalogue_chunk_27 : ((allPermutationLists.drop 2700).take 100).all cataloguePredicate = true := by
  decide +kernel

#print axioms catalogue_chunk_27

theorem catalogue_chunk_28 : ((allPermutationLists.drop 2800).take 100).all cataloguePredicate = true := by
  decide +kernel

#print axioms catalogue_chunk_28

theorem catalogue_chunk_29 : ((allPermutationLists.drop 2900).take 100).all cataloguePredicate = true := by
  decide +kernel

#print axioms catalogue_chunk_29

theorem catalogue_chunk_30 : ((allPermutationLists.drop 3000).take 100).all cataloguePredicate = true := by
  decide +kernel

#print axioms catalogue_chunk_30

theorem catalogue_chunk_31 : ((allPermutationLists.drop 3100).take 100).all cataloguePredicate = true := by
  decide +kernel

#print axioms catalogue_chunk_31

theorem catalogue_chunk_32 : ((allPermutationLists.drop 3200).take 100).all cataloguePredicate = true := by
  decide +kernel

#print axioms catalogue_chunk_32

theorem catalogue_chunk_33 : ((allPermutationLists.drop 3300).take 100).all cataloguePredicate = true := by
  decide +kernel

#print axioms catalogue_chunk_33

theorem catalogue_chunk_34 : ((allPermutationLists.drop 3400).take 100).all cataloguePredicate = true := by
  decide +kernel

#print axioms catalogue_chunk_34

theorem catalogue_chunk_35 : ((allPermutationLists.drop 3500).take 100).all cataloguePredicate = true := by
  decide +kernel

#print axioms catalogue_chunk_35

theorem catalogue_chunk_36 : ((allPermutationLists.drop 3600).take 100).all cataloguePredicate = true := by
  decide +kernel

#print axioms catalogue_chunk_36

theorem catalogue_chunk_37 : ((allPermutationLists.drop 3700).take 100).all cataloguePredicate = true := by
  decide +kernel

#print axioms catalogue_chunk_37

theorem catalogue_chunk_38 : ((allPermutationLists.drop 3800).take 100).all cataloguePredicate = true := by
  decide +kernel

#print axioms catalogue_chunk_38

theorem catalogue_chunk_39 : ((allPermutationLists.drop 3900).take 100).all cataloguePredicate = true := by
  decide +kernel

#print axioms catalogue_chunk_39

theorem catalogue_chunk_40 : ((allPermutationLists.drop 4000).take 100).all cataloguePredicate = true := by
  decide +kernel

#print axioms catalogue_chunk_40

theorem catalogue_chunk_41 : ((allPermutationLists.drop 4100).take 100).all cataloguePredicate = true := by
  decide +kernel

#print axioms catalogue_chunk_41

theorem catalogue_chunk_42 : ((allPermutationLists.drop 4200).take 100).all cataloguePredicate = true := by
  decide +kernel

#print axioms catalogue_chunk_42

theorem catalogue_chunk_43 : ((allPermutationLists.drop 4300).take 100).all cataloguePredicate = true := by
  decide +kernel

#print axioms catalogue_chunk_43

theorem catalogue_chunk_44 : ((allPermutationLists.drop 4400).take 100).all cataloguePredicate = true := by
  decide +kernel

#print axioms catalogue_chunk_44

theorem catalogue_chunk_45 : ((allPermutationLists.drop 4500).take 100).all cataloguePredicate = true := by
  decide +kernel

#print axioms catalogue_chunk_45

theorem catalogue_chunk_46 : ((allPermutationLists.drop 4600).take 100).all cataloguePredicate = true := by
  decide +kernel

#print axioms catalogue_chunk_46

theorem catalogue_chunk_47 : ((allPermutationLists.drop 4700).take 100).all cataloguePredicate = true := by
  decide +kernel

#print axioms catalogue_chunk_47

theorem catalogue_chunk_48 : ((allPermutationLists.drop 4800).take 100).all cataloguePredicate = true := by
  decide +kernel

#print axioms catalogue_chunk_48

theorem catalogue_chunk_49 : ((allPermutationLists.drop 4900).take 100).all cataloguePredicate = true := by
  decide +kernel

#print axioms catalogue_chunk_49

theorem catalogue_chunk_50 : (allPermutationLists.drop 5000).all cataloguePredicate = true := by
  decide +kernel

#print axioms catalogue_chunk_50

/-- Every one of the 5040 basis permutations has one of the 30 incidence words. -/
theorem catalogue_coverage (p : Equiv.Perm Label) :
    ∃ i : Fin 30, ∀ t : Fin 35, incidence p t = incidence (representatives i) t := by
  have hcheck : allPermutationLists.all (fun q =>
      catalogueWords.contains (List.ofFn (incidence (listMap q)))) = true := by
    have h50 := catalogue_chunk_50
    have h49 := catalogue_chunk_step allPermutationLists cataloguePredicate 4900
      catalogue_chunk_49 h50
    have h48 := catalogue_chunk_step allPermutationLists cataloguePredicate 4800
      catalogue_chunk_48 h49
    have h47 := catalogue_chunk_step allPermutationLists cataloguePredicate 4700
      catalogue_chunk_47 h48
    have h46 := catalogue_chunk_step allPermutationLists cataloguePredicate 4600
      catalogue_chunk_46 h47
    have h45 := catalogue_chunk_step allPermutationLists cataloguePredicate 4500
      catalogue_chunk_45 h46
    have h44 := catalogue_chunk_step allPermutationLists cataloguePredicate 4400
      catalogue_chunk_44 h45
    have h43 := catalogue_chunk_step allPermutationLists cataloguePredicate 4300
      catalogue_chunk_43 h44
    have h42 := catalogue_chunk_step allPermutationLists cataloguePredicate 4200
      catalogue_chunk_42 h43
    have h41 := catalogue_chunk_step allPermutationLists cataloguePredicate 4100
      catalogue_chunk_41 h42
    have h40 := catalogue_chunk_step allPermutationLists cataloguePredicate 4000
      catalogue_chunk_40 h41
    have h39 := catalogue_chunk_step allPermutationLists cataloguePredicate 3900
      catalogue_chunk_39 h40
    have h38 := catalogue_chunk_step allPermutationLists cataloguePredicate 3800
      catalogue_chunk_38 h39
    have h37 := catalogue_chunk_step allPermutationLists cataloguePredicate 3700
      catalogue_chunk_37 h38
    have h36 := catalogue_chunk_step allPermutationLists cataloguePredicate 3600
      catalogue_chunk_36 h37
    have h35 := catalogue_chunk_step allPermutationLists cataloguePredicate 3500
      catalogue_chunk_35 h36
    have h34 := catalogue_chunk_step allPermutationLists cataloguePredicate 3400
      catalogue_chunk_34 h35
    have h33 := catalogue_chunk_step allPermutationLists cataloguePredicate 3300
      catalogue_chunk_33 h34
    have h32 := catalogue_chunk_step allPermutationLists cataloguePredicate 3200
      catalogue_chunk_32 h33
    have h31 := catalogue_chunk_step allPermutationLists cataloguePredicate 3100
      catalogue_chunk_31 h32
    have h30 := catalogue_chunk_step allPermutationLists cataloguePredicate 3000
      catalogue_chunk_30 h31
    have h29 := catalogue_chunk_step allPermutationLists cataloguePredicate 2900
      catalogue_chunk_29 h30
    have h28 := catalogue_chunk_step allPermutationLists cataloguePredicate 2800
      catalogue_chunk_28 h29
    have h27 := catalogue_chunk_step allPermutationLists cataloguePredicate 2700
      catalogue_chunk_27 h28
    have h26 := catalogue_chunk_step allPermutationLists cataloguePredicate 2600
      catalogue_chunk_26 h27
    have h25 := catalogue_chunk_step allPermutationLists cataloguePredicate 2500
      catalogue_chunk_25 h26
    have h24 := catalogue_chunk_step allPermutationLists cataloguePredicate 2400
      catalogue_chunk_24 h25
    have h23 := catalogue_chunk_step allPermutationLists cataloguePredicate 2300
      catalogue_chunk_23 h24
    have h22 := catalogue_chunk_step allPermutationLists cataloguePredicate 2200
      catalogue_chunk_22 h23
    have h21 := catalogue_chunk_step allPermutationLists cataloguePredicate 2100
      catalogue_chunk_21 h22
    have h20 := catalogue_chunk_step allPermutationLists cataloguePredicate 2000
      catalogue_chunk_20 h21
    have h19 := catalogue_chunk_step allPermutationLists cataloguePredicate 1900
      catalogue_chunk_19 h20
    have h18 := catalogue_chunk_step allPermutationLists cataloguePredicate 1800
      catalogue_chunk_18 h19
    have h17 := catalogue_chunk_step allPermutationLists cataloguePredicate 1700
      catalogue_chunk_17 h18
    have h16 := catalogue_chunk_step allPermutationLists cataloguePredicate 1600
      catalogue_chunk_16 h17
    have h15 := catalogue_chunk_step allPermutationLists cataloguePredicate 1500
      catalogue_chunk_15 h16
    have h14 := catalogue_chunk_step allPermutationLists cataloguePredicate 1400
      catalogue_chunk_14 h15
    have h13 := catalogue_chunk_step allPermutationLists cataloguePredicate 1300
      catalogue_chunk_13 h14
    have h12 := catalogue_chunk_step allPermutationLists cataloguePredicate 1200
      catalogue_chunk_12 h13
    have h11 := catalogue_chunk_step allPermutationLists cataloguePredicate 1100
      catalogue_chunk_11 h12
    have h10 := catalogue_chunk_step allPermutationLists cataloguePredicate 1000
      catalogue_chunk_10 h11
    have h9 := catalogue_chunk_step allPermutationLists cataloguePredicate 900
      catalogue_chunk_09 h10
    have h8 := catalogue_chunk_step allPermutationLists cataloguePredicate 800
      catalogue_chunk_08 h9
    have h7 := catalogue_chunk_step allPermutationLists cataloguePredicate 700
      catalogue_chunk_07 h8
    have h6 := catalogue_chunk_step allPermutationLists cataloguePredicate 600
      catalogue_chunk_06 h7
    have h5 := catalogue_chunk_step allPermutationLists cataloguePredicate 500
      catalogue_chunk_05 h6
    have h4 := catalogue_chunk_step allPermutationLists cataloguePredicate 400
      catalogue_chunk_04 h5
    have h3 := catalogue_chunk_step allPermutationLists cataloguePredicate 300
      catalogue_chunk_03 h4
    have h2 := catalogue_chunk_step allPermutationLists cataloguePredicate 200
      catalogue_chunk_02 h3
    have h1 := catalogue_chunk_step allPermutationLists cataloguePredicate 100
      catalogue_chunk_01 h2
    have h0 := catalogue_chunk_step allPermutationLists cataloguePredicate 0
      catalogue_chunk_00 h1
    simpa only [List.drop_zero] using h0
  have hp := List.all_eq_true.mp hcheck (List.ofFn p) (ofFn_mem_allPermutationLists p)
  rw [listMap_ofFn, catalogueWords_eq] at hp
  have hm := List.contains_iff.mp hp
  obtain ⟨i, _, hi⟩ := List.mem_map.mp hm
  refine ⟨i, fun t => ?_⟩
  exact congrFun (List.ofFn_injective hi).symm t

def probes10 : Fin 10 → Fin 35 := ![0, 4, 6, 8, 13, 17, 22, 24, 28, 34]
def probes18 : Fin 18 → Fin 35 := ![1, 3, 9, 11, 12, 14, 15, 17, 19, 21, 22, 24, 25, 27, 28, 30, 32, 34]

def word10 (i : Fin 30) : Fin 10 → Bool :=
  fun j => incidence (representatives i) (probes10 j)

def word18 (i : Fin 30) : Fin 18 → Bool :=
  fun j => incidence (representatives i) (probes18 j)

theorem ten_probes_injective : Function.Injective word10 := by
  decide +kernel

/-- Each of the 35 possible incidence queries is positive in exactly six planes. -/
theorem catalogue_column_weight : ∀ t : Fin 35,
    (∑ i : Fin 30, if incidence (representatives i) t then 1 else 0) = 6 := by
  decide +kernel

def distance {n : ℕ} (a b : Fin n → Bool) : ℕ :=
  ∑ j, if a j = b j then 0 else 1

theorem eighteen_distance : ∀ i j : Fin 30,
    i ≠ j → 3 ≤ distance (word18 i) (word18 j) := by
  decide +kernel

theorem distance_triangle {n : ℕ} (a b c : Fin n → Bool) :
    distance a c ≤ distance a b + distance b c := by
  unfold distance
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  cases a j <;> cases b j <;> cases c j <;> decide

theorem distance_symm {n : ℕ} (a b : Fin n → Bool) : distance a b = distance b a := by
  unfold distance
  apply Finset.sum_congr rfl
  intro j _
  simp only [eq_comm]

/-- A received 18-bit word has at most one catalogue plane within one bit error. -/
theorem one_error_unique (received : Fin 18 → Bool) (i j : Fin 30)
    (hi : distance (word18 i) received ≤ 1)
    (hj : distance (word18 j) received ≤ 1) : i = j := by
  by_contra hne
  have hl := eighteen_distance i j hne
  have ht := distance_triangle (word18 i) received (word18 j)
  rw [distance_symm received (word18 j)] at ht
  omega

/-- Ten fixed actual associator-zero queries determine the whole hidden incidence. -/
theorem ten_probes_reconstruct (p q : Equiv.Perm Label)
    (h : ∀ j : Fin 10, actualResponse p (probes10 j) = actualResponse q (probes10 j)) :
    ∀ t : Fin 35, actualResponse p t = actualResponse q t := by
  obtain ⟨i, hi⟩ := catalogue_coverage p
  obtain ⟨k, hk⟩ := catalogue_coverage q
  have hw : word10 i = word10 k := by
    funext j
    have hj := h j
    rw [actualResponse_eq_incidence, actualResponse_eq_incidence, hi, hk] at hj
    exact hj
  have hik := ten_probes_injective hw
  intro t
  rw [actualResponse_eq_incidence, actualResponse_eq_incidence, hi, hk, hik]

/-- Eighteen fixed actual probes reconstruct incidence even with one wrong answer.
This determines the incidence plane, not an orientation or a basis permutation. -/
theorem eighteen_probes_reconstruct_with_one_error (p q : Equiv.Perm Label)
    (received : Fin 18 → Bool)
    (hp : distance (fun j => actualResponse p (probes18 j)) received ≤ 1)
    (hq : distance (fun j => actualResponse q (probes18 j)) received ≤ 1) :
    ∀ t : Fin 35, actualResponse p t = actualResponse q t := by
  obtain ⟨i, hi⟩ := catalogue_coverage p
  obtain ⟨k, hk⟩ := catalogue_coverage q
  have hpi : (fun j => actualResponse p (probes18 j)) = word18 i := by
    funext j
    rw [actualResponse_eq_incidence]
    exact hi (probes18 j)
  have hqk : (fun j => actualResponse q (probes18 j)) = word18 k := by
    funext j
    rw [actualResponse_eq_incidence]
    exact hk (probes18 j)
  rw [hpi] at hp
  rw [hqk] at hq
  have hik := one_error_unique received i k hp hq
  intro t
  rw [actualResponse_eq_incidence, actualResponse_eq_incidence, hi, hk, hik]

/-- No choice of eight fixed triple queries separates all catalogue planes. -/
theorem eight_fixed_probes_insufficient (probes : Fin 8 → Fin 35) :
    ¬ Function.Injective (fun i : Fin 30 => fun j : Fin 8 =>
      incidence (representatives i) (probes j)) := by
  apply MathResearch.ProbeLowerBound.eight_probes_impossible
  intro j
  exact catalogue_column_weight (probes j)

theorem at_most_eight_fixed_probes_insufficient {n : ℕ} (hn : n ≤ 8)
    (probes : Fin n → Fin 35) :
    ¬ Function.Injective (fun i : Fin 30 => fun j : Fin n =>
      incidence (representatives i) (probes j)) := by
  apply MathResearch.ProbeLowerBound.at_most_eight_probes_impossible hn
  intro j
  exact catalogue_column_weight (probes j)

#print axioms basis_associator_zero_iff
#print axioms actualResponse_eq_incidence
#print axioms representatives_bijective
#print axioms listMap_ofFn
#print axioms ofFn_mem_allPermutationLists
#print axioms catalogueWords_eq
#print axioms catalogue_coverage
#print axioms ten_probes_injective
#print axioms catalogue_column_weight
#print axioms eighteen_distance
#print axioms distance_triangle
#print axioms distance_symm
#print axioms one_error_unique
#print axioms ten_probes_reconstruct
#print axioms eighteen_probes_reconstruct_with_one_error
#print axioms eight_fixed_probes_insufficient
#print axioms at_most_eight_fixed_probes_insufficient
end MathResearch.OctonionIncidence
