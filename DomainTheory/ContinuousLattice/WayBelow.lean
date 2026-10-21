/-ai
This file gathers and re-exports the way-below development: Scott-open sets and the fact that a Scott-open set is an upper set, the universe, binary intersections, and arbitrary unions of Scott-open sets, the way-below relation and the clauses of Proposition 2.2, openness of a way-below upset, the characterization of elements way below themselves, the supremum form of way-below, the expression of an element as the supremum of the elements way below it, directedness of that set, interpolation, the two neighbourhood-basis forms, the infimum of a Scott-open neighbourhood, and Proposition 2.4.
ai-/
module

public import DomainTheory.ContinuousLattice.WayBelow.Basic
public import DomainTheory.ContinuousLattice.WayBelow.ScottOpenu2eisUpperSet
public import DomainTheory.ContinuousLattice.WayBelow.scottOpen_univ
public import DomainTheory.ContinuousLattice.WayBelow.scottOpen_inter
public import DomainTheory.ContinuousLattice.WayBelow.scottOpen_sUnion
public import DomainTheory.ContinuousLattice.WayBelow.WayBelowu2ele
public import DomainTheory.ContinuousLattice.WayBelow.bot_wayBelow
public import DomainTheory.ContinuousLattice.WayBelow.WayBelowu2etrans_le
public import DomainTheory.ContinuousLattice.WayBelow.WayBelowu2ele_trans
public import DomainTheory.ContinuousLattice.WayBelow.WayBelowu2esup
public import DomainTheory.ContinuousLattice.WayBelow.scottOpen_wayBelow
public import DomainTheory.ContinuousLattice.WayBelow.wayBelow_self_iff_scottOpen_Ici
public import DomainTheory.ContinuousLattice.WayBelow.wayBelow_sSup_iff
public import DomainTheory.ContinuousLattice.WayBelow.IsContinuousLatticeu2esSup_wayBelow
public import DomainTheory.ContinuousLattice.WayBelow.directedOn_wayBelow
public import DomainTheory.ContinuousLattice.WayBelow.wayBelow_interpolate
public import DomainTheory.ContinuousLattice.WayBelow.exists_wayBelow_subset
public import DomainTheory.ContinuousLattice.WayBelow.exists_wayBelow_Ici_subset
public import DomainTheory.ContinuousLattice.WayBelow.sInf_wayBelow
public import DomainTheory.ContinuousLattice.WayBelow.isContinuousLattice_iff_isLUB_sInf_nhds

@[expose] public section
