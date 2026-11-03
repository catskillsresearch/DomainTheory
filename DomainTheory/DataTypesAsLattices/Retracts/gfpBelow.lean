module

public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Pomega.eDense
public import DomainTheory.DataTypesAsLattices.Retracts.Fixpoints

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def gfpBelow (f : Pomega → Pomega) (b : Pomega) : Pomega :=
  ⋃₀ {x | x ⊆ f x ∩ b}

namespace gfpBelow

theorem subset (f : Pomega → Pomega) (b : Pomega) :
    gfpBelow f b ⊆ b := by
  intro k hk
  obtain ⟨x, hx, hkx⟩ := Set.mem_sUnion.mp hk
  exact (hx hkx).2

theorem postfixed {f : Pomega → Pomega} (hf : IsScottContinuous f)
    (b : Pomega) : gfpBelow f b ⊆ f (gfpBelow f b) ∩ b := by
  intro k hk
  obtain ⟨x, hx, hkx⟩ := Set.mem_sUnion.mp hk
  have hxz : x ⊆ gfpBelow f b := fun _ hm => Set.mem_sUnion.mpr ⟨x, hx, hm⟩
  exact ⟨IsScottContinuous.monotone hf hxz (hx hkx).1, (hx hkx).2⟩

theorem le {f : Pomega → Pomega} (_hf : IsScottContinuous f) (b : Pomega)
    (_hb : f b ⊆ b) : gfpBelow f b ⊆ b :=
  subset f b

theorem fixed_inter {f : Pomega → Pomega} (hf : IsScottContinuous f)
    (b : Pomega) : f (gfpBelow f b) ∩ b = gfpBelow f b := by
  apply subset_antisymm
  · intro k hk
    refine Set.mem_sUnion.mpr ⟨f (gfpBelow f b) ∩ b, ?_, hk⟩
    have hle : gfpBelow f b ⊆ f (gfpBelow f b) ∩ b := postfixed hf b
    have : f (gfpBelow f b) ⊆ f (f (gfpBelow f b) ∩ b) :=
      IsScottContinuous.monotone hf hle
    intro m hm
    exact ⟨this hm.1, hm.2⟩
  · exact postfixed hf b

theorem isGLB {f : Pomega → Pomega} (_hf : IsScottContinuous f)
    {A : Set Pomega} (_hA : A ⊆ Fixpoints f) {z : Pomega}
    (hz : f z = z) (hlb : ∀ x ∈ A, z ⊆ x) :
    z ⊆ gfpBelow f (⋂₀ A) := by
  have hzI : z ⊆ ⋂₀ A := fun k hk y hy => hlb y hy hk
  have hpost : z ⊆ f z ∩ ⋂₀ A := fun k hk => ⟨by rwa [hz], hzI hk⟩
  exact fun k hk => Set.mem_sUnion.mpr ⟨z, hpost, hk⟩

theorem mem (f : Pomega → Pomega) (hf : IsScottContinuous f)
    (A : Set Pomega) (hA : A ⊆ Fixpoints f) :
    gfpBelow f (⋂₀ A) ∈ Fixpoints f := by
  let z := gfpBelow f (⋂₀ A)
  have hinter : f z ∩ ⋂₀ A = z := fixed_inter hf (⋂₀ A)
  have hzle : z ⊆ ⋂₀ A := subset f (⋂₀ A)
  have hfz : f z ⊆ ⋂₀ A := by
    intro k hk y hy
    have hzy : z ⊆ y := subset_trans hzle (Set.sInter_subset_of_mem hy)
    have : k ∈ f y := IsScottContinuous.monotone hf hzy hk
    have hyf : f y = y := hA hy
    rwa [hyf] at this
  have : f z ∩ ⋂₀ A = f z := Set.inter_eq_left.mpr hfz
  change f z = z
  rwa [this] at hinter

end gfpBelow

end DomainTheory.DataTypesAsLattices
