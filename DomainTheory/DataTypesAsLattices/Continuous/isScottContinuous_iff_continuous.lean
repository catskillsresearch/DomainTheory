/-ai
A map f from Pω to Pω is Scott continuous if and only if it is continuous for the positive topology.

If f is Scott continuous, continuity into the generated topology reduces to showing that the preimage of each subbasic open is open, and Scott opens coincide with opens. The preimage of the subbasic open of k is the union of the basic neighbourhoods of those codes n for which k lies in f of the finite set coded by n: membership of k in f(x) is membership in the Scott union, which supplies such a code, and the converse uses monotonicity. If instead f is topologically continuous, compare membership of k in f(x) with membership in the Scott union. The preimage of the subbasic open of k is open, hence Scott open. If k lies in f(x), that preimage contains a basic neighbourhood of some finite subset of x, and evaluating at the finite set itself puts k in f of that finite set. If k lies in the Scott union, the witnessing finite set lies in the preimage, and a Scott open is an upper set, so x lies in the preimage.
ai-/
module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Order
public import DomainTheory.DataTypesAsLattices.Pomega
public import DomainTheory.DataTypesAsLattices.Continuous.Basic
public import DomainTheory.DataTypesAsLattices.Continuous.isScottOpen_isUpper
public import DomainTheory.DataTypesAsLattices.Continuous.mem_scottUnion
public import DomainTheory.DataTypesAsLattices.Continuous.isScottContinuous_monotone
public import DomainTheory.DataTypesAsLattices.Continuous.isOpen_memOpen
public import DomainTheory.DataTypesAsLattices.Continuous.isScottOpen_iff_isOpen

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace


/-- Scott continuity coincides with topological continuity `Pω → Pω`. -/
theorem isScottContinuous_iff_continuous (f : Pomega → Pomega) :
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
      have : k ∈ scottUnion f x := by rwa [← hf x]
      obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp this
      exact Set.mem_iUnion₂.mpr ⟨n, hkn, hn⟩
    · intro hx
      obtain ⟨n, hkn, hn⟩ := Set.mem_iUnion₂.mp hx
      exact isScottContinuous_monotone hf hn hkn
  · intro hfcont x
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

end DomainTheory.DataTypesAsLattices
