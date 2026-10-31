import StructureInput
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Homeomorph.Defs

-- atlas-structure-source-sha256: f6caebe6a85beaca8e5d5cfd0bb3fcd8f1ee18f0b134604f2ee212cbbf3c1a75
noncomputable def SpectrumBridge.alphaF {R : Type*} [CommRing R] (b w : Polynomial R) : MvPolynomial (Fin 3) R →+* MvPolynomial (Fin 3) R :=
  MvPolynomial.eval₂Hom MvPolynomial.C (Arxiv261038474.graphSubtract b w)

noncomputable def SpectrumBridge.alphaG {R : Type*} [CommRing R] (b w : Polynomial R) : MvPolynomial (Fin 3) R →+* MvPolynomial (Fin 3) R :=
  MvPolynomial.eval₂Hom MvPolynomial.C (Arxiv261038474.graphRestore b w)

noncomputable def SpectrumBridge.axisIdeal (R : Type*) [CommRing R] : Ideal (MvPolynomial (Fin 3) R) :=
  Ideal.span ({MvPolynomial.X 1, MvPolynomial.X 2} : Set (MvPolynomial (Fin 3) R))

noncomputable def SpectrumBridge.graphIdeal {R : Type*} [CommRing R] (b w : Polynomial R) : Ideal (MvPolynomial (Fin 3) R) :=
  Ideal.span ({MvPolynomial.X 0 - Arxiv261038474.univariate b 1,
    MvPolynomial.X 2 - Arxiv261038474.univariate w 1} : Set (MvPolynomial (Fin 3) R))

def SpectrumBridge.vanishing {R : Type*} [CommRing R] (I : Ideal (MvPolynomial (Fin 3) R)) : Set (PrimeSpectrum (MvPolynomial (Fin 3) R)) :=
  {p | I ≤ p.asIdeal}

theorem SpectrumBridge.substitution_inverses : ∀ {R : Type*} [CommRing R] (b w : Polynomial R),
  (SpectrumBridge.alphaG b w).comp (SpectrumBridge.alphaF b w) = RingHom.id (MvPolynomial (Fin 3) R) ∧
  (SpectrumBridge.alphaF b w).comp (SpectrumBridge.alphaG b w) = RingHom.id (MvPolynomial (Fin 3) R) := by
  intro R _ b w
  constructor
  · ext i m <;> first
    | simpa [SpectrumBridge.alphaF, SpectrumBridge.alphaG, Arxiv261038474.compose] using
        congrArg (MvPolynomial.coeff m) (congrFun (Arxiv261038474.subtract_restore b w) i)
    | simp [SpectrumBridge.alphaF, SpectrumBridge.alphaG]
  · ext i m <;> first
    | simpa [SpectrumBridge.alphaF, SpectrumBridge.alphaG, Arxiv261038474.compose] using
        congrArg (MvPolynomial.coeff m) (congrFun (Arxiv261038474.restore_subtract b w) i)
    | simp [SpectrumBridge.alphaF, SpectrumBridge.alphaG]

theorem SpectrumBridge.ideal_transport : ∀ {R : Type*} [CommRing R] (b w : Polynomial R),
  Ideal.map (SpectrumBridge.alphaF b w) (SpectrumBridge.axisIdeal R) = SpectrumBridge.graphIdeal b w := by
  intro R _ b w
  simp [SpectrumBridge.axisIdeal, SpectrumBridge.graphIdeal, Ideal.map_span,
    SpectrumBridge.alphaF, Arxiv261038474.graphSubtract, Set.image_insert_eq,
    Set.image_singleton]

theorem SpectrumBridge.coordinate_and_spectrum_equivalence : ∀ {R : Type*} [CommRing R] (b w : Polynomial R),
  ∃ e : MvPolynomial (Fin 3) R ≃ₐ[R] MvPolynomial (Fin 3) R,
    e.toAlgHom.toRingHom = SpectrumBridge.alphaF b w ∧
    e.symm.toAlgHom.toRingHom = SpectrumBridge.alphaG b w ∧
    ∃ h : PrimeSpectrum (MvPolynomial (Fin 3) R) ≃ₜ PrimeSpectrum (MvPolynomial (Fin 3) R),
      (h : PrimeSpectrum (MvPolynomial (Fin 3) R) → PrimeSpectrum (MvPolynomial (Fin 3) R)) =
        (fun p => PrimeSpectrum.comap (SpectrumBridge.alphaF b w) p) ∧
      (h.symm : PrimeSpectrum (MvPolynomial (Fin 3) R) → PrimeSpectrum (MvPolynomial (Fin 3) R)) =
        (fun p => PrimeSpectrum.comap (SpectrumBridge.alphaG b w) p) ∧
      h '' SpectrumBridge.vanishing (SpectrumBridge.graphIdeal b w) =
        SpectrumBridge.vanishing (SpectrumBridge.axisIdeal R) := by
  intro R _ b w
  obtain ⟨hGF, hFG⟩ := SpectrumBridge.substitution_inverses b w
  have hgf (x : MvPolynomial (Fin 3) R) :
      SpectrumBridge.alphaG b w (SpectrumBridge.alphaF b w x) = x :=
    DFunLike.congr_fun hGF x
  have hfg (x : MvPolynomial (Fin 3) R) :
      SpectrumBridge.alphaF b w (SpectrumBridge.alphaG b w x) = x :=
    DFunLike.congr_fun hFG x
  let e : MvPolynomial (Fin 3) R ≃ₐ[R] MvPolynomial (Fin 3) R :=
    { toFun := SpectrumBridge.alphaF b w
      invFun := SpectrumBridge.alphaG b w
      left_inv := hgf
      right_inv := hfg
      map_mul' := (SpectrumBridge.alphaF b w).map_mul
      map_add' := (SpectrumBridge.alphaF b w).map_add
      commutes' := by
        intro r
        change SpectrumBridge.alphaF b w (MvPolynomial.C r) = MvPolynomial.C r
        simp [SpectrumBridge.alphaF] }
  have hl (p : PrimeSpectrum (MvPolynomial (Fin 3) R)) :
      PrimeSpectrum.comap (SpectrumBridge.alphaG b w)
        (PrimeSpectrum.comap (SpectrumBridge.alphaF b w) p) = p := by
    apply PrimeSpectrum.ext
    apply Ideal.ext
    intro x
    change SpectrumBridge.alphaF b w (SpectrumBridge.alphaG b w x) ∈ p.asIdeal ↔ x ∈ p.asIdeal
    rw [hfg]
  have hr (p : PrimeSpectrum (MvPolynomial (Fin 3) R)) :
      PrimeSpectrum.comap (SpectrumBridge.alphaF b w)
        (PrimeSpectrum.comap (SpectrumBridge.alphaG b w) p) = p := by
    apply PrimeSpectrum.ext
    apply Ideal.ext
    intro x
    change SpectrumBridge.alphaG b w (SpectrumBridge.alphaF b w x) ∈ p.asIdeal ↔ x ∈ p.asIdeal
    rw [hgf]
  let h : PrimeSpectrum (MvPolynomial (Fin 3) R) ≃ₜ PrimeSpectrum (MvPolynomial (Fin 3) R) :=
    { toFun := PrimeSpectrum.comap (SpectrumBridge.alphaF b w)
      invFun := PrimeSpectrum.comap (SpectrumBridge.alphaG b w)
      left_inv := hl
      right_inv := hr
      continuous_toFun := (PrimeSpectrum.comap (SpectrumBridge.alphaF b w)).continuous
      continuous_invFun := (PrimeSpectrum.comap (SpectrumBridge.alphaG b w)).continuous }
  refine ⟨e, rfl, rfl, h, rfl, rfl, ?_⟩
  have hv (p : PrimeSpectrum (MvPolynomial (Fin 3) R)) :
      p ∈ SpectrumBridge.vanishing (SpectrumBridge.graphIdeal b w) ↔
      h p ∈ SpectrumBridge.vanishing (SpectrumBridge.axisIdeal R) := by
    change SpectrumBridge.graphIdeal b w ≤ p.asIdeal ↔
      SpectrumBridge.axisIdeal R ≤ Ideal.comap (SpectrumBridge.alphaF b w) p.asIdeal
    rw [← SpectrumBridge.ideal_transport b w]
    exact Ideal.map_le_iff_le_comap
  apply Set.ext
  intro p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact (hv q).mp hq
  · intro hp
    refine ⟨h.symm p, ?_, h.apply_symm_apply p⟩
    apply (hv (h.symm p)).mpr
    simpa only [h.apply_symm_apply] using hp

