module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition_7_1

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Factoid_1_8
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_13

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

/- concordance: source L5159 EXERCISE 8.14 closure operators -/
/-- **Exercise 8.14 (Scott 1981, PRG-19), the definition.** A retraction `a : E → E` is a
*closure operator* iff `I_E ⊑ a`, i.e. `a` is inflationary. -/
class ClosureOperator (a : ApproximableMap E E) : Prop where
  out : Retraction a ∧ idMap E ≤ a

section ClosureOperator

variable {a : ApproximableMap E E}

/-- **Compactness of a fixed point w.r.t. directed unions of `Fix(a)`.** Phrased via the ambient
`E.Element` order and `iSupDirected` (since `Fix(a)` is not itself a `NeighborhoodSystem.Element`
type), mirroring `Theorem85.lean`'s `IsCompactElt`. -/
def IsCompactFix (_h : ClosureOperator a) (y : FixSet a) : Prop :=
  ∀ {I : Type u} [Nonempty I] (d : I → FixSet a)
    (hdir : ∀ i j, ∃ k, (d i).1 ≤ (d k).1 ∧ (d j).1 ≤ (d k).1),
    y.1 ≤ iSupDirected (fun i => (d i).1) hdir → ∃ i, y.1 ≤ (d i).1

end ClosureOperator

section FiniteDomain

variable {a : ApproximableMap E E} (h : ClosureOperator a)

/-- The compact ("finite") fixed points of `a`, as a subtype of `Fix(a)`. -/
def CompactFix (h : ClosureOperator a) := {y : FixSet a // IsCompactFix h y}

end FiniteDomain

section ClosureOperator

variable {a : ApproximableMap E E}

/-- **The bottom of `Fix(a)`**: `a(⊥)`. -/
def botFix (h : ClosureOperator a) : FixSet a :=
  ⟨a.toElementMap ⊥, toElementMap_idem h.out.1 ⊥⟩

/-- **`a(⊥)` is the least element of `Fix(a)`**: `a(⊥) ⊑ y` for every `y ∈ Fix(a)`. Since `⊥ ⊑ y`
always, monotonicity gives `a(⊥) ⊑ a(y) = y`. -/
theorem botFix_le (h : ClosureOperator a) (y : FixSet a) : (botFix h).1 ≤ y.1 := by
  have h1 : a.toElementMap ⊥ ≤ a.toElementMap y.1 := a.toElementMap_mono bot_le
  rwa [y.2] at h1

/-- `botFix` is compact: it is below *every* element of `Fix(a)` (`botFix_le`), so trivially below
any particular member of a (non-empty) directed family. -/
theorem isCompactFix_botFix (h : ClosureOperator a) : IsCompactFix h (botFix h) := by
  intro I _ d _ _
  obtain ⟨i0⟩ := (inferInstance : Nonempty I)
  exact ⟨i0, botFix_le h (d i0)⟩

end ClosureOperator

section FiniteDomain

variable {a : ApproximableMap E E} (h : ClosureOperator a)

/-- The bottom compact fixed point `a(⊥)`. -/
def botK : CompactFix h := ⟨botFix h, isCompactFix_botFix h⟩

end FiniteDomain

section ClosureOperator

variable {a : ApproximableMap E E}

/-- Unfolding `I_E ⊑ a` at the element level (Theorem 3.13(i)): `y ⊑ a(y)` for every `y`. -/
theorem le_toElementMap_of_isClosureOperator (h : ClosureOperator a) (y : E.Element) :
    y ≤ a.toElementMap y := by
  have h1 := (le_iff_toElementMap_le.mp h.out.2) y
  rwa [toElementMap_idMap] at h1

/-- **Finite joins of compacts are compact.** If `y₁, y₂ ∈ Fix(a)` are compact and bounded above
(in `E`), their join `a(⊔{y₁,y₂})` (`⊔` = Exercise 1.27's `sSup`) is again compact: if it sits below
a directed union, so do `y₁` and `y₂` individually (they are `⊑ a(⊔{y₁,y₂})` since `⊔ ⊑ a(⊔)` by
inflation), compactness places each below some member of the family, directedness finds a common
one, and the join being *least* upper bound of `{y₁,y₂}` (composed with `a`) transfers the bound. -/
theorem isCompactFix_sup (h : ClosureOperator a) {y1 y2 : FixSet a}
    (hc1 : IsCompactFix h y1) (hc2 : IsCompactFix h y2)
    (hb : E.Bounded ({y1.1, y2.1} : Set E.Element)) :
    IsCompactFix h ⟨a.toElementMap (E.sSup {y1.1, y2.1} hb), toElementMap_idem h.out.1 _⟩ := by
  intro I _ d hdir hle
  have hs_le : E.sSup {y1.1, y2.1} hb ≤ iSupDirected (fun i => (d i).1) hdir :=
    (le_toElementMap_of_isClosureOperator h _).trans hle
  have h1le : y1.1 ≤ iSupDirected (fun i => (d i).1) hdir :=
    (E.le_sSup {y1.1, y2.1} hb (by simp)).trans hs_le
  have h2le : y2.1 ≤ iSupDirected (fun i => (d i).1) hdir :=
    (E.le_sSup {y1.1, y2.1} hb (by simp)).trans hs_le
  obtain ⟨i1, hi1⟩ := hc1 d hdir h1le
  obtain ⟨i2, hi2⟩ := hc2 d hdir h2le
  obtain ⟨k, hk1, hk2⟩ := hdir i1 i2
  have hle1 : y1.1 ≤ (d k).1 := hi1.trans hk1
  have hle2 : y2.1 ≤ (d k).1 := hi2.trans hk2
  have hsup_le : E.sSup {y1.1, y2.1} hb ≤ (d k).1 :=
    E.sSup_le {y1.1, y2.1} hb (by rintro x (rfl | rfl) <;> assumption)
  refine ⟨k, ?_⟩
  have h3 := a.toElementMap_mono hsup_le
  rwa [(d k).2] at h3

/-- **The key new fact.** `a(↑X)`, for any `E`-neighbourhood `X`, is compact w.r.t. directed unions
*within `Fix(a)`* — even though it need not be principal in `E` itself. Proof: if
`a(↑X) ⊑ ⋃ᵢ d(i)` then (since `↑X ⊑ a(↑X)` by inflation) `↑X ⊑ ⋃ᵢ d(i)`, so by compactness of `↑X`
in `E` (`principal_isCompactElt`), `↑X ⊑ d(i)` for some `i`; applying `a` (monotone) and using that
`d(i)` is already fixed gives `a(↑X) ⊑ d(i)`. -/
theorem isCompactFix_toElementMap_principal (h : ClosureOperator a) {X : Set α} (hX : E.mem X) :
    IsCompactFix h ⟨a.toElementMap (E.principal hX), toElementMap_idem h.out.1 _⟩ := by
  intro I _ d hdir hle
  have hle' : E.principal hX ≤ iSupDirected (fun i => (d i).1) hdir :=
    (le_toElementMap_of_isClosureOperator h (E.principal hX)).trans hle
  obtain ⟨i, hi⟩ := principal_isCompactElt hX (fun i => (d i).1) hdir hle'
  refine ⟨i, ?_⟩
  have h2 := a.toElementMap_mono hi
  rwa [(d i).2] at h2

end ClosureOperator

section FiniteDomain

variable {a : ApproximableMap E E} (h : ClosureOperator a)

/-- The generator of a compact fixed point from an `E`-neighbourhood `X`. -/
def genK {X : Set α} (hX : E.mem X) : CompactFix h :=
  ⟨⟨a.toElementMap (E.principal hX), toElementMap_idem h.out.1 _⟩,
    isCompactFix_toElementMap_principal h hX⟩

/-- The join of two compact fixed points bounded above by a common `y ∈ Fix(a)`. -/
def joinCompactFix {k1 k2 : CompactFix h} {y : FixSet a}
    (hk1y : k1.1.1 ≤ y.1) (hk2y : k2.1.1 ≤ y.1) : CompactFix h :=
  ⟨⟨a.toElementMap (E.sSup {k1.1.1, k2.1.1} ⟨y.1, by rintro x (rfl | rfl) <;> assumption⟩),
      toElementMap_idem h.out.1 _⟩,
    isCompactFix_sup h k1.2 k2.2 ⟨y.1, by rintro x (rfl | rfl) <;> assumption⟩⟩

theorem joinCompactFix_le {k1 k2 : CompactFix h} {y : FixSet a}
    (hk1y : k1.1.1 ≤ y.1) (hk2y : k2.1.1 ≤ y.1) : (joinCompactFix h hk1y hk2y).1.1 ≤ y.1 := by
  have hb : E.Bounded ({k1.1.1, k2.1.1} : Set E.Element) :=
    ⟨y.1, by rintro x (rfl | rfl) <;> assumption⟩
  have hsup_le : E.sSup {k1.1.1, k2.1.1} hb ≤ y.1 :=
    E.sSup_le {k1.1.1, k2.1.1} hb (by rintro x (rfl | rfl) <;> assumption)
  have h1 := a.toElementMap_mono hsup_le
  rwa [y.2] at h1

/-- The principal up-set of a compact fixed point `k`: `{q ∣ k ⊑ q}`. This is the "neighbourhood"
of `k` in the reconstructed system (smaller compacts give *bigger* up-sets, matching the
information-order convention `Factoid 1.7a`). -/
def upFix (k : CompactFix h) : Set (CompactFix h) := {q | k.1.1 ≤ q.1.1}

@[simp] theorem mem_upFix {k q : CompactFix h} : q ∈ upFix h k ↔ k.1.1 ≤ q.1.1 := Iff.rfl

theorem self_mem_upFix (k : CompactFix h) : k ∈ upFix h k := (mem_upFix h).mpr (le_refl _)

theorem upFix_antitone {k k' : CompactFix h} (hkk' : k.1.1 ≤ k'.1.1) :
    upFix h k' ⊆ upFix h k :=
  fun _ hq => hkk'.trans hq

/-- The generator of a non-empty up-set is unique. -/
theorem upFix_injOn {k k' : CompactFix h} (heq : upFix h k = upFix h k') : k.1.1 = k'.1.1 :=
  le_antisymm ((Set.ext_iff.mp heq k').mpr (self_mem_upFix h k'))
    ((Set.ext_iff.mp heq k).mp (self_mem_upFix h k))

/-- **The key algebraic identity**: the intersection of two principal up-sets, when jointly
bounded by some `y`, is again a principal up-set — of the join. -/
theorem upFix_inter (k1 k2 : CompactFix h) {y : FixSet a}
    (hk1y : k1.1.1 ≤ y.1) (hk2y : k2.1.1 ≤ y.1) :
    upFix h k1 ∩ upFix h k2 = upFix h (joinCompactFix h hk1y hk2y) := by
  have hb : E.Bounded ({k1.1.1, k2.1.1} : Set E.Element) :=
    ⟨y.1, by rintro x (rfl | rfl) <;> assumption⟩
  apply Set.ext
  intro q
  simp only [mem_upFix, Set.mem_inter_iff, joinCompactFix]
  constructor
  · rintro ⟨h1q, h2q⟩
    have hb' : E.Bounded ({k1.1.1, k2.1.1} : Set E.Element) :=
      ⟨q.1.1, by rintro x (rfl | rfl) <;> assumption⟩
    have hsup_le : E.sSup {k1.1.1, k2.1.1} hb' ≤ q.1.1 :=
      E.sSup_le {k1.1.1, k2.1.1} hb' (by rintro x (rfl | rfl) <;> assumption)
    have h3 := a.toElementMap_mono hsup_le
    rwa [q.1.2] at h3
  · intro hjq
    refine ⟨?_, ?_⟩
    · exact ((E.le_sSup {k1.1.1, k2.1.1} hb (by simp)).trans
        (le_toElementMap_of_isClosureOperator h _)).trans hjq
    · exact ((E.le_sSup {k1.1.1, k2.1.1} hb (by simp)).trans
        (le_toElementMap_of_isClosureOperator h _)).trans hjq

theorem upFix_subset_upFix_botK (k : CompactFix h) : upFix h k ⊆ upFix h (botK h) :=
  fun q _ => botFix_le h q.1

/-- **The reconstructed neighbourhood system.** Tokens are the compact fixed points of `a`;
neighbourhoods are their principal up-sets. -/
def domainOfClosure (h : ClosureOperator a) : NeighborhoodSystem (CompactFix h) where
  mem S := ∃ k : CompactFix h, S = upFix h k
  master := upFix h (botK h)
  master_nonempty := ⟨botK h, self_mem_upFix h (botK h)⟩
  master_mem := ⟨botK h, rfl⟩
  sub_master := by rintro S ⟨k, rfl⟩; exact upFix_subset_upFix_botK h k
  inter_mem := by
    rintro S1 S2 Z ⟨k1, rfl⟩ ⟨k2, rfl⟩ ⟨k3, rfl⟩ hZsub
    obtain ⟨hk13, hk23⟩ := hZsub (self_mem_upFix h k3)
    exact ⟨joinCompactFix h hk13 hk23, upFix_inter h k1 k2 hk13 hk23⟩

/-- The compact fixed points confirmed by a filter `g` of `domainOfClosure h`. -/
def confirmedIdx (g : (domainOfClosure h).Element) := {k : CompactFix h // g.mem (upFix h k)}

instance instNonemptyConfirmedIdx (g : (domainOfClosure h).Element) :
    Nonempty (confirmedIdx h g) :=
  ⟨⟨botK h, g.master_mem⟩⟩

theorem confirmedIdx_directed (g : (domainOfClosure h).Element) :
    ∀ i j : confirmedIdx h g, ∃ k : confirmedIdx h g,
      i.1.1.1 ≤ k.1.1.1 ∧ j.1.1.1 ≤ k.1.1.1 := by
  rintro ⟨k1, hk1⟩ ⟨k2, hk2⟩
  have hint : g.mem (upFix h k1 ∩ upFix h k2) := g.inter_mem hk1 hk2
  obtain ⟨k3, hk3eq⟩ := g.sub hint
  rw [hk3eq] at hint
  have hmem3 : k3 ∈ upFix h k1 ∩ upFix h k2 := hk3eq ▸ self_mem_upFix h k3
  exact ⟨⟨k3, hint⟩, hmem3.1, hmem3.2⟩

/-- **The backward map `|domainOfClosure h| → Fix(a)`**: the directed union of all confirmed
compacts. -/
def fromElementFilter (g : (domainOfClosure h).Element) : FixSet a :=
  ⟨iSupDirected (fun i : confirmedIdx h g => i.1.1.1) (confirmedIdx_directed h g),
    toElementMap_iSupDirected_fixed _ (confirmedIdx_directed h g) (fun i => i.1.1.2)⟩

/-- The family `a(↑X)`, for `X` ranging over the (principal-approximant) neighbourhoods of `y.1`. -/
def genFamily (y : FixSet a) (i : {X : Set α // y.1.mem X}) : FixSet a :=
  (genK h (y.1.sub i.2)).1

theorem genFamily_directed (y : FixSet a) :
    ∀ i j : {X : Set α // y.1.mem X}, ∃ k, (genFamily h y i).1 ≤ (genFamily h y k).1 ∧
      (genFamily h y j).1 ≤ (genFamily h y k).1 := by
  intro i j
  obtain ⟨k, hik, hjk⟩ := principalFamily_directed y.1 i j
  exact ⟨k, a.toElementMap_mono hik, a.toElementMap_mono hjk⟩

/-- **The forward map `Fix(a) → |domainOfClosure h|`**: `y ↦ {S ∣ S = ↑k ∧ k ⊑ y}`. -/
def toElementFilter (y : FixSet a) : (domainOfClosure h).Element where
  mem S := ∃ k : CompactFix h, S = upFix h k ∧ k.1.1 ≤ y.1
  sub := fun ⟨k, hSeq, _⟩ => ⟨k, hSeq⟩
  master_mem := ⟨botK h, rfl, botFix_le h y⟩
  inter_mem := by
    rintro S1 S2 ⟨k1, rfl, hk1y⟩ ⟨k2, rfl, hk2y⟩
    exact ⟨joinCompactFix h hk1y hk2y, upFix_inter h k1 k2 hk1y hk2y, joinCompactFix_le h hk1y hk2y⟩
  up_mem := by
    rintro S1 S2 ⟨k1, rfl, hk1y⟩ hS2mem hsub
    obtain ⟨k2, rfl⟩ := hS2mem
    exact ⟨k2, rfl, (mem_upFix h |>.mp (hsub (self_mem_upFix h k1))).trans hk1y⟩

theorem le_of_toElementFilter_le {y y' : FixSet a}
    (hle : toElementFilter h y ≤ toElementFilter h y') : y.1 ≤ y'.1 := by
  intro X hXy
  have hX : E.mem X := y.1.sub hXy
  have hky : (toElementFilter h y).mem (upFix h (genK h hX)) := by
    refine ⟨genK h hX, rfl, ?_⟩
    have h1 : E.principal hX ≤ y.1 := principal_le_of_mem hXy
    have h2 := a.toElementMap_mono h1
    rwa [y.2] at h2
  obtain ⟨k', hkk', hk'y'⟩ := hle _ hky
  have hkeq : (genK h hX).1.1 = k'.1.1 := upFix_injOn h hkk'
  have h1 : E.principal hX ≤ a.toElementMap (E.principal hX) :=
    le_toElementMap_of_isClosureOperator h _
  rw [show a.toElementMap (E.principal hX) = k'.1.1 from hkeq] at h1
  exact (h1.trans hk'y') X ((E.mem_principal hX).mpr ⟨hX, subset_rfl⟩)

theorem toElementFilter_fromElementFilter (g : (domainOfClosure h).Element) :
    toElementFilter h (fromElementFilter h g) = g := by
  apply Element.ext
  intro S
  constructor
  · rintro ⟨k0, rfl, hk0⟩
    obtain ⟨i, hi⟩ := k0.2 (fun i : confirmedIdx h g => i.1.1) (confirmedIdx_directed h g) hk0
    exact g.up_mem i.2 ⟨k0, rfl⟩ (upFix_antitone h hi)
  · intro hS
    obtain ⟨k0, rfl⟩ := g.sub hS
    exact ⟨k0, rfl, le_iSupDirected _ (confirmedIdx_directed h g) ⟨k0, hS⟩⟩

theorem toElementFilter_mono {y y' : FixSet a} (hyy' : y.1 ≤ y'.1) :
    toElementFilter h y ≤ toElementFilter h y' :=
  fun _ ⟨k, hSeq, hky⟩ => ⟨k, hSeq, hky.trans hyy'⟩

/-- **`y` is the directed union of `a(↑X)` for `X ∈ y`.** Apply `a` (continuous, `toElementMap_
iSupDirected`) to `E`'s own algebraicity decomposition (`eq_iSupDirected_principal`) of `y.1`, then
use `a(y.1) = y.1`. -/
theorem toElementMap_eq_iSupDirected_genFamily (y : FixSet a) :
    y.1 = iSupDirected (fun i => (genFamily h y i).1) (genFamily_directed h y) := by
  have h1 : a.toElementMap y.1 = iSupDirected (fun i => (genFamily h y i).1) (genFamily_directed h y) := by
    conv_lhs => rw [eq_iSupDirected_principal y.1]
    exact toElementMap_iSupDirected a _ (principalFamily_directed y.1)
  rw [y.2] at h1
  exact h1

theorem fromElementFilter_toElementFilter (y : FixSet a) :
    fromElementFilter h (toElementFilter h y) = y := by
  apply Subtype.ext
  show iSupDirected (fun i : confirmedIdx h (toElementFilter h y) => i.1.1.1)
      (confirmedIdx_directed h (toElementFilter h y)) = y.1
  apply le_antisymm
  · apply iSupDirected_le
    rintro ⟨k, k', hkk', hk'y⟩
    exact (upFix_injOn h hkk' ▸ hk'y : k.1.1 ≤ y.1)
  · rw [toElementMap_eq_iSupDirected_genFamily h y]
    apply iSupDirected_le
    intro i
    have hk : (toElementFilter h y).mem (upFix h (genK h (y.1.sub i.2))) := by
      refine ⟨genK h (y.1.sub i.2), rfl, ?_⟩
      have h1 : E.principal (y.1.sub i.2) ≤ y.1 := principal_le_of_mem i.2
      have h2 := a.toElementMap_mono h1
      rwa [y.2] at h2
    exact le_iSupDirected (fun i : confirmedIdx h (toElementFilter h y) => i.1.1.1)
      (confirmedIdx_directed h (toElementFilter h y)) ⟨genK h (y.1.sub i.2), hk⟩

/-- **Exercise 8.14, the domain isomorphism.** `Fix(a)` is order-isomorphic to
`|domainOfClosure h|`. -/
def fixSetOrderIso (h : ClosureOperator a) : FixSet a ≃o (domainOfClosure h).Element where
  toFun := toElementFilter h
  invFun := fromElementFilter h
  left_inv := fromElementFilter_toElementFilter h
  right_inv := toElementFilter_fromElementFilter h
  map_rel_iff' := by
    intro y y'
    exact ⟨le_of_toElementFilter_le h, toElementFilter_mono h⟩

/-- **Exercise 8.14, the final question, answered exactly.** `y ∈ Fix(a)` is compact (i.e. is a
*finite element* of the fixed-point domain) **iff** `y = a(↑X)` for a single `E`-neighbourhood `X`.
The forward direction is a sandwich argument: `y` is the directed union of the compacts `a(↑X)`
(`X ∈ y`, `toElementMap_eq_iSupDirected_genFamily`), so compactness pulls out a single witness `X`
with `y ⊑ a(↑X)`; the reverse inequality `a(↑X) ⊑ y` is automatic since `X ∈ y`. -/
theorem isCompactFix_iff (y : FixSet a) :
    IsCompactFix h y ↔ ∃ (X : Set α) (hX : E.mem X), y.1 = a.toElementMap (E.principal hX) := by
  constructor
  · intro hc
    obtain ⟨i, hi⟩ := hc (genFamily h y) (genFamily_directed h y)
      (le_of_eq (toElementMap_eq_iSupDirected_genFamily h y))
    have hX : E.mem i.1 := y.1.sub i.2
    refine ⟨i.1, hX, le_antisymm hi ?_⟩
    have h1 : E.principal hX ≤ y.1 := principal_le_of_mem i.2
    have h2 := a.toElementMap_mono h1
    rwa [y.2] at h2
  · rintro ⟨X, hX, hy⟩
    exact hy ▸ isCompactFix_toElementMap_principal h hX

/-- **Exercise 8.14 (Scott 1981, PRG-19), the main theorem.** For any closure operator
`a : E → E`, the fixed-point set of `a` is a finitary domain. -/
theorem isFinitary_of_isClosureOperator (h : ClosureOperator a) : IsFinitary a :=
  ⟨CompactFix h, domainOfClosure h, ⟨fixSetOrderIso h⟩⟩

end FiniteDomain

end

set_option linter.unusedVariables false

theorem example_814.{u} : And
  (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E}
    (h : @DomainTheory.NeighbourhoodSystems.ClosureOperator α E a)
    (y : @DomainTheory.NeighbourhoodSystems.FixSet α E a),
    Iff (@DomainTheory.NeighbourhoodSystems.IsCompactFix α E a h y)
      (∃ (X : Set α) (hX : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α E X),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
          (@Subtype.val (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
            (fun (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E) =>
              @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E E a y) y)
            y)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E E a
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal α E X hX))))
  (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E},
    @DomainTheory.NeighbourhoodSystems.ClosureOperator α E a → @DomainTheory.NeighbourhoodSystems.IsFinitary α E a) :=
  @And.intro
  (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E}
    (h : @DomainTheory.NeighbourhoodSystems.ClosureOperator α E a)
    (y : @DomainTheory.NeighbourhoodSystems.FixSet α E a),
    Iff (@DomainTheory.NeighbourhoodSystems.IsCompactFix α E a h y)
      (∃ (X : Set α) (hX : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α E X),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
          (@Subtype.val (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
            (fun (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E) =>
              @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E E a y) y)
            y)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E E a
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal α E X hX))))
  (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E},
    @DomainTheory.NeighbourhoodSystems.ClosureOperator α E a → @DomainTheory.NeighbourhoodSystems.IsFinitary α E a)
  @DomainTheory.NeighbourhoodSystems.isCompactFix_iff @DomainTheory.NeighbourhoodSystems.isFinitary_of_isClosureOperator

end DomainTheory.NeighbourhoodSystems
