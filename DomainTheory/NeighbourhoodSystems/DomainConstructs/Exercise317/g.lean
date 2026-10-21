/-ai
The decoding map from the infinite iterate of the truth system to the binary system relates W to X when W is an iterate neighbourhood and X is the cone of a string whose encoding contains W. The domain and codomain laws are that membership and cone membership. The masters are related by the empty string. For an intersection of two cones, agreement of the encodings makes the strings comparable, and the intersection is the smaller cone. A smaller cone is a shorter prefix, and encoding reverses prefixes, so the smaller neighbourhood remains inside the shorter encoding.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.T
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.encSet
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.mem_encSet
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.encSet_nil
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.encSet_anti
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.encSet_agree
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.comparable_of_agree

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise317

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap

/-- **The decoding map `g : T^∞ → B`.** Relates `W` to the cone `τΣ*` exactly when `W ⊆ encSet τ`,
i.e. `W` pins the first `|τ|` copies to `τ`. -/
def g : ApproximableMap (iterSys T) B where
  rel W X := (iterSys T).mem W ∧ ∃ τ, X = cone τ ∧ W ⊆ encSet τ
  rel_dom h := h.1
  rel_cod := fun ⟨_, τ, hX, _⟩ => hX ▸ memB_cone τ
  master_rel := ⟨(iterSys T).master_mem, [], cone_nil.symm, by rw [encSet_nil]; exact Set.subset_univ _⟩
  inter_right := by
    rintro W X X' ⟨hW, τ, hX, hWτ⟩ ⟨_, τ', hX', hWτ'⟩
    subst hX; subst hX'
    rcases comparable_of_agree (fun i b b' => encSet_agree hW hWτ hWτ') with hpre | hpre
    · exact ⟨hW, τ', by rw [Set.inter_eq_right.mpr (cone_subset_cone.mpr hpre)], hWτ'⟩
    · exact ⟨hW, τ, by rw [Set.inter_eq_left.mpr (cone_subset_cone.mpr hpre)], hWτ⟩
  mono := by
    rintro W W₂ X X₂ ⟨_, τ, hX, hWτ⟩ hW₂W hXX₂ hW₂ hX₂
    obtain ⟨τ₂, rfl⟩ := hX₂
    subst hX
    have hpre : τ₂ <+: τ := cone_subset_cone.mp hXX₂
    exact ⟨hW₂, τ₂, rfl, hW₂W.trans (hWτ.trans (encSet_anti hpre))⟩

end DomainTheory.NeighbourhoodSystems.Exercise317
