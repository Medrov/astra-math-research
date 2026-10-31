import StructureInput
import Mathlib.Algebra.Algebra.Equiv

-- atlas-structure-source-sha256: f6caebe6a85beaca8e5d5cfd0bb3fcd8f1ee18f0b134604f2ee212cbbf3c1a75
noncomputable def Arxiv261038474.substitutionAlgHom {R : Type*} [CommRing R]
    (H : Fin 3 → MvPolynomial (Fin 3) R) :
    MvPolynomial (Fin 3) R →ₐ[R] MvPolynomial (Fin 3) R :=
  MvPolynomial.aeval H

theorem Arxiv261038474.substitutionAlgHom_toRingHom : ∀ {R : Type*} [CommRing R]
    (H : Fin 3 → MvPolynomial (Fin 3) R),
  (Arxiv261038474.substitutionAlgHom H).toRingHom =
    MvPolynomial.eval₂Hom MvPolynomial.C H := by
  intro R _ H
  apply RingHom.ext
  intro p
  change MvPolynomial.aeval H p =
    MvPolynomial.eval₂Hom (algebraMap R (MvPolynomial (Fin 3) R)) H p
  exact MvPolynomial.aeval_eq_eval₂Hom (f := H) p

theorem Arxiv261038474.substitutionAlgHom_comp : ∀ {R : Type*} [CommRing R]
    (H K : Fin 3 → MvPolynomial (Fin 3) R),
  (Arxiv261038474.substitutionAlgHom K).comp
      (Arxiv261038474.substitutionAlgHom H) =
    Arxiv261038474.substitutionAlgHom (Arxiv261038474.compose H K) := by
  intro R _ H K
  ext i : 1
  simpa only [AlgHom.comp_apply, Arxiv261038474.substitutionAlgHom,
    MvPolynomial.aeval_X, Arxiv261038474.compose] using
    congrArg (fun f : MvPolynomial (Fin 3) R →+* MvPolynomial (Fin 3) R => f (H i))
      (Arxiv261038474.substitutionAlgHom_toRingHom K)

theorem Arxiv261038474.graph_substitution_inverse_identities : ∀ {R : Type*} [CommRing R] (b w : Polynomial R),
  ((Arxiv261038474.substitutionAlgHom
      (Arxiv261038474.graphRestore b w)).comp
      (Arxiv261038474.substitutionAlgHom
        (Arxiv261038474.graphSubtract b w)) =
    AlgHom.id R (MvPolynomial (Fin 3) R)) ∧
  ((Arxiv261038474.substitutionAlgHom
      (Arxiv261038474.graphSubtract b w)).comp
      (Arxiv261038474.substitutionAlgHom
        (Arxiv261038474.graphRestore b w)) =
    AlgHom.id R (MvPolynomial (Fin 3) R)) := by
  intro R _ b w
  have hX : Arxiv261038474.substitutionAlgHom
      (MvPolynomial.X : Fin 3 → MvPolynomial (Fin 3) R) =
      AlgHom.id R (MvPolynomial (Fin 3) R) := by
    ext i
    simp [Arxiv261038474.substitutionAlgHom]
  constructor
  · rw [Arxiv261038474.substitutionAlgHom_comp,
      Arxiv261038474.subtract_restore]
    exact hX
  · rw [Arxiv261038474.substitutionAlgHom_comp,
      Arxiv261038474.restore_subtract]
    exact hX

theorem Arxiv261038474.coordinate_automorphism_exists : ∀ {R : Type*} [CommRing R] (b w : Polynomial R),
  ∃ α : MvPolynomial (Fin 3) R ≃ₐ[R] MvPolynomial (Fin 3) R,
    (∀ p : MvPolynomial (Fin 3) R,
      α p = MvPolynomial.eval₂Hom MvPolynomial.C
        (Arxiv261038474.graphSubtract b w) p) ∧
    (∀ p : MvPolynomial (Fin 3) R,
      α.symm p = MvPolynomial.eval₂Hom MvPolynomial.C
        (Arxiv261038474.graphRestore b w) p) := by
  intro R _ b w
  have h := Arxiv261038474.graph_substitution_inverse_identities b w
  let α : MvPolynomial (Fin 3) R ≃ₐ[R] MvPolynomial (Fin 3) R :=
    AlgEquiv.ofAlgHom
      (Arxiv261038474.substitutionAlgHom (Arxiv261038474.graphSubtract b w))
      (Arxiv261038474.substitutionAlgHom (Arxiv261038474.graphRestore b w))
      (by first | exact h.1 | exact h.2)
      (by first | exact h.1 | exact h.2)
  refine ⟨α, ?_, ?_⟩
  · intro p
    change Arxiv261038474.substitutionAlgHom (Arxiv261038474.graphSubtract b w) p = _
    exact congrArg
      (fun f : MvPolynomial (Fin 3) R →+* MvPolynomial (Fin 3) R => f p)
      (Arxiv261038474.substitutionAlgHom_toRingHom (Arxiv261038474.graphSubtract b w))
  · intro p
    change Arxiv261038474.substitutionAlgHom (Arxiv261038474.graphRestore b w) p = _
    exact congrArg
      (fun f : MvPolynomial (Fin 3) R →+* MvPolynomial (Fin 3) R => f p)
      (Arxiv261038474.substitutionAlgHom_toRingHom (Arxiv261038474.graphRestore b w))

