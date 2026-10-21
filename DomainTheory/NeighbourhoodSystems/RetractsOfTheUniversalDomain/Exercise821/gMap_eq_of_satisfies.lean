/-ai
A strict map from the tree algebra of a neighbourhood system to another that agrees with a given catamorphism on leaves and on nodes is equal to that catamorphism.

The neighbourhood relation of the map agrees with the graph relation of the catamorphism, by induction on membership in the tree algebra, generalized over the output neighbourhood. At the master, strictness gives one direction and the master clause forces the output to be master. At a leaf, the leaf equation at the principal element, rewritten by the principal-leaf identity, matches the two relations. At a node, the pairing equation and the principal-node identity do the same, and the inductive hypotheses identify the recursive outputs. Off the tree algebra neither relation holds, and extensionality of approximable maps finishes the argument.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.inSharp_principal
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.pairSharp_principal

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example61 Proposition77 Exercise717 Exercise510

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

variable {hD : ∀ X, D.mem X → X.Nonempty}

variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}

/-- **Uniqueness of the catamorphism** (Exercise 8.21(b)(1), Scott's own remark "`g` is unique
because the values on finite elements are fixed"). Any *strict* `k : D^§ → E` satisfying `gMap`'s two
defining equations at the *element* level — `k(x^§) = u(x)` and `k(⟨y,z⟩) = v(⟨k(y),k(z)⟩)` — is
literally the catamorphism `gMap u v hD`. Proved by induction on the `MemS`-derivation of the input
neighbourhood, generalizing over the output: the `Γ` case is strictness plus `master_rel`; the leaf
case reads the hypothesis off at the principal element `↑X` via `inSharp_principal` and
`rel_iff_mem_principal`; the node case does the same with `pairSharp_principal`, using the induction
hypotheses to identify the two recursive outputs. -/
theorem gMap_eq_of_satisfies {k : ApproximableMap (Dsharp D hD) E} (hk : IsStrict k)
    (hu : ∀ x : D.Element, k.toElementMap (inSharp D hD x) = u.toElementMap x)
    (hv : ∀ y z : (Dsharp D hD).Element,
      k.toElementMap (pairSharp D hD y z)
        = v.toElementMap (pair (k.toElementMap y) (k.toElementMap z))) :
    k = gMap u v hD := by
  have main : ∀ {W}, MemS D W → ∀ Z, k.rel W Z ↔ GRel u v W Z := by
    intro W hW
    induction hW with
    | gamma =>
        intro Z
        constructor
        · intro h; exact GRel.gamma (hk h)
        · intro h
          have hZ : Z = E.master := gRel_gamma_inv hD h
          subst hZ
          exact k.master_rel
    | @zero X hX =>
        intro Z
        have key := hu (D.principal hX)
        rw [inSharp_principal hX] at key
        constructor
        · intro h
          have h1 := (rel_iff_mem_principal k (MemS.zero hX)).mp h
          rw [key] at h1
          exact GRel.leaf ((rel_iff_mem_principal u hX).mpr h1)
        · intro h
          have h1 := (rel_iff_mem_principal u hX).mp (gRel_embZero_inv hD h)
          rw [← key] at h1
          exact (rel_iff_mem_principal k (MemS.zero hX)).mpr h1
    | @pair P Q hP hQ ihP ihQ =>
        intro Z
        have key := hv ((Dsharp D hD).principal hP) ((Dsharp D hD).principal hQ)
        rw [pairSharp_principal hP hQ] at key
        constructor
        · intro h
          have h1 := (rel_iff_mem_principal k (MemS.pair hP hQ)).mp h
          rw [key] at h1
          obtain ⟨V, hVmem, hVrel⟩ := h1
          obtain ⟨Z1, Z2, hZ1, hZ2, rfl⟩ := hVmem
          have hkZ1 : k.rel P Z1 := (rel_iff_mem_principal k hP).mpr hZ1
          have hkZ2 : k.rel Q Z2 := (rel_iff_mem_principal k hQ).mpr hZ2
          exact GRel.node ((ihP Z1).mp hkZ1) ((ihQ Z2).mp hkZ2) hVrel
        · intro h
          obtain ⟨Z1, Z2, hg1, hg2, hvrel⟩ := gRel_embPair_inv hD h
          have h1 := (rel_iff_mem_principal k hP).mp ((ihP Z1).mpr hg1)
          have h2 := (rel_iff_mem_principal k hQ).mp ((ihQ Z2).mpr hg2)
          have h3 : (v.toElementMap (pair (k.toElementMap ((Dsharp D hD).principal hP))
              (k.toElementMap ((Dsharp D hD).principal hQ)))).mem Z :=
            ⟨prodNbhd Z1 Z2, ⟨Z1, Z2, h1, h2, rfl⟩, hvrel⟩
          rw [← key] at h3
          exact (rel_iff_mem_principal k (MemS.pair hP hQ)).mpr h3
  apply ApproximableMap.ext
  intro W Z
  by_cases hW : MemS D W
  · exact main hW Z
  · exact ⟨fun h => absurd (k.rel_dom h) hW, fun h => absurd (gRel_dom h) hW⟩

end DomainTheory.NeighbourhoodSystems
