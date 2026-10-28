module

public import Mathlib.Topology.Bases
public import DomainTheory.DataTypesAsLattices.Continuous.scottUnion
public import DomainTheory.DataTypesAsLattices.Continuous.mem_scottUnion
public import DomainTheory.DataTypesAsLattices.Continuous.isScottOpen_isUpper
public import DomainTheory.DataTypesAsLattices.Continuous.isScottOpen_iff_isOpen
public import Mathlib.Data.Set.Lattice.Indexed
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottOpen
public import DomainTheory.DataTypesAsLattices.Continuous.scottPiece
public import DomainTheory.DataTypesAsLattices.Continuous.memOpen
public import DomainTheory.DataTypesAsLattices.Continuous.basicNhhd

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

class IsScottContinuous (f : Pomega → Pomega) : Prop where
  out : ∀ x, f x = scottUnion f x

namespace IsScottContinuous

theorem monotone {f : Pomega → Pomega}
    (hf : IsScottContinuous f) {x y : Pomega} (h : x ⊆ y) : f x ⊆ f y := by
  intro m hm
  rw [hf.out x, mem_scottUnion] at hm
  rw [hf.out y, mem_scottUnion]
  obtain ⟨n, hn, hmn⟩ := hm
  exact ⟨n, subset_trans hn h, hmn⟩

theorem determined {f g : Pomega → Pomega}
    (hf : IsScottContinuous f) (hg : IsScottContinuous g)
    (hfin : ∀ n, f (e n) = g (e n)) : f = g := by
  funext x
  rw [hf.out x, hg.out x]
  simp [scottUnion, scottPiece, hfin]

theorem iff_continuous (f : Pomega → Pomega) :
    IsScottContinuous f ↔ Continuous f := by
  constructor
  · intro hf
    refine continuous_generateFrom_iff.2 ?_
    rintro _ ⟨k, rfl⟩
    rw [← isScottOpen_iff_isOpen]
    refine ⟨{n | k ∈ f (e n)}, ?_⟩
    ext x
    constructor
    · intro hx
      have : k ∈ scottUnion f x := by rwa [← hf.out x]
      obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp this
      exact Set.mem_iUnion₂.mpr ⟨n, hkn, hn⟩
    · intro hx
      obtain ⟨n, hkn, hn⟩ := Set.mem_iUnion₂.mp hx
      exact monotone hf hn hkn
  · intro hfcont
    constructor
    intro x
    ext k
    have hopen : IsScottOpen (f ⁻¹' memOpen k) :=
      (isScottOpen_iff_isOpen _).mpr (IsOpen.preimage hfcont (isOpen_memOpen k))
    constructor
    · intro hk
      obtain ⟨B, hB⟩ := hopen
      have hx : x ∈ ⋃ n ∈ B, basicNhhd n := by
        have : x ∈ f ⁻¹' memOpen k := hk
        rwa [hB] at this
      obtain ⟨n, hn, hxn⟩ := Set.mem_iUnion₂.mp hx
      have hen : k ∈ f (e n) := by
        have : e n ∈ f ⁻¹' memOpen k := by
          rw [hB]
          exact Set.mem_iUnion₂.mpr ⟨n, hn, (subset_rfl : e n ⊆ e n)⟩
        exact this
      exact mem_scottUnion.mpr ⟨n, hxn, hen⟩
    · intro hk
      obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp hk
      have : e n ∈ f ⁻¹' memOpen k := hkn
      exact isScottOpen_isUpper hopen this hn

end IsScottContinuous

end DomainTheory.DataTypesAsLattices
