//! 
//! OSmosis DAG Specification
//! 
//! This module defines the specification of the OSmosis model and a state machine defining the
//! atomic transitions between valid model states.
//! 
//! ---------------------------------------------------------------------
//! System Graph :- { nodes: Set<Node>, edges: Set<Edge> }
//! Node :- ProtectionDomain | Resource(Type) | ResourceSpace(Type)
//! Edge :- HoldEdge | MapEdge | SubsetEdge | RequestEdge
//! EdgeAttribute :- Type | Perms
//! ResourceType :- Virtual | Physical
//! Perms :- Read | Write | Execute | Terminate 
//! ---------------------------------------------------------------------
//! ^ OSmosis model definition from SOSP 2025 submission
//!

use vstd::prelude::{verus, nat, admit, Set};
use state_machines_macros::*;

verus!
{

// --------------------------------------- Graph --------------------------------------------------
state_machine!
{
osmosis {

fields {
    /// The protection domains of the Osmosis DAG
    pub domains: Set<ProtectionDomain>,
    /// The resources of the Osmosis DAG
    pub resources: Set<Resource>,
    /// The resource spaces of the Osmosis DAG
    pub spaces: Set<ResourceSpace>,
    /// The Hold edges of the Osmosis DAG
    pub holds: Set<HoldEdge>,
    /// The Map edges of the Osmosis DAG
    pub maps: Set<MapEdge>,
    /// The Subset edges of the Osmosis DAG
    pub subsets: Set<SubsetEdge>,
    /// The Request edges of the Osmosis DAG
    pub requests: Set<RequestEdge>,
}

// ------------------------------- Structural Invariants ------------------------------------------
// We define structural invariants to be those which guarantee that it's a well formed directed
// acyclic graph (DAG) that is connected.

/// The model must have a finite number of protection domains
#[invariant]
pub open spec fn domains_is_finite(&self) -> bool {
    self.domains.finite()
}

/// The model must have a finite number of resources
#[invariant]
pub open spec fn resources_is_finite(&self) -> bool {
    self.resources.finite()
}

/// The model must have a finite number of resource spaces
#[invariant]
pub open spec fn spaces_is_finite(&self) -> bool {
    self.spaces.finite()
}

/// The model must have a finite number of hold edges
#[invariant]
pub open spec fn holds_is_finite(&self) -> bool {
    self.holds.finite()
}

/// The model must have a finite number of map edges
#[invariant]
pub open spec fn maps_is_finite(&self) -> bool {
    self.maps.finite()
}

/// The model must have a finite number of subset edges
#[invariant]
pub open spec fn subsets_is_finite(&self) -> bool {
    self.subsets.finite()
}

/// The model must have a finite number of request edges
#[invariant]
pub open spec fn requests_is_finite(&self) -> bool {
    self.requests.finite()
}

/// Hold edges must be between nodes in the graph
#[invariant]
pub open spec fn hold_nodes_in_graph(&self) -> bool {
    forall |h| #[trigger] self.holds.contains(h) ==> {
        &&& self.domains.contains(h.src())
        &&& h.dst() is Resource ==> self.resources.contains(h.dst()->res)
        &&& h.dst() is Space ==> self.spaces.contains(h.dst()->space)
    }
} 

/// Map edges must be between nodes in the graph
#[invariant]
pub open spec fn map_nodes_in_graph(&self) -> bool {
    forall |m| self.maps.contains(m) ==> {
        match m {
            MapEdge::SpaceBacking { sb_src, sb_dst } => {
                &&& self.spaces.contains(sb_src)
                &&& self.resources.contains(sb_dst)
            }
            MapEdge::SpaceMap { sm_src, sm_dst } => {
                &&& self.spaces.contains(sm_src)
                &&& self.spaces.contains(sm_dst)
            }
            MapEdge::ResourceMap { rm_src, rm_dst } => {
                &&& self.resources.contains(rm_src)
                &&& self.resources.contains(rm_dst)
            }
        }
    }   
} 

/// Subset edges must be between nodes in the graph
#[invariant]
pub open spec fn subset_nodes_in_graph(&self) -> bool {
    forall |s| #[trigger] self.subsets.contains(s) ==> {
        &&& self.resources.contains(s.src())
        &&& self.spaces.contains(s.dst())
    }  
}

/// Request edges must be between nodes in the graph
#[invariant]
pub open spec fn request_nodes_in_graph(&self) -> bool {
    forall |r| #[trigger] self.requests.contains(r) ==> {
        &&& self.domains.contains(r.src())
        &&& self.domains.contains(r.dst())
    }
}

/// Hold edge to each resource in the graph
#[invariant]
pub open spec fn all_resources_are_held(&self) -> bool {
    forall |r: Resource| self.resources.contains(r) ==> 
        exists |h: HoldEdge| self.holds.contains(h) && #[trigger] h.dst() == ResourceLike::Resource { res: r }
}

/// Hold edge to each resource space in the graph
#[invariant]
pub open spec fn all_spaces_are_held(&self) -> bool {
    forall |s: ResourceSpace| self.spaces.contains(s) ==>
        exists |h: HoldEdge| self.holds.contains(h) && #[trigger] h.dst() == ResourceLike::Space { space: s }
}

/// Subset edge from each resource to a resource space in the graph
#[invariant]
pub open spec fn all_resources_subset_spaces(&self) -> bool {
    forall |r: Resource| self.resources.contains(r) ==>
        exists |se: SubsetEdge| self.subsets.contains(se) && #[trigger] se.src() == r
}

// --------------------------------------- Resource Value Invariants ------------------------------
// Our current modelling of resources and spaces includes a numeric value that is unique to each 
// resource allocation (and the spaces have a set of values that are unique to them), that are
// supposed to model the set of values managed by the space and allocated out as resources. This
// addition, seemed useful to me, as it might help us make arguments around resource depletion, but
// clearly not all resources have a finite set of values, so for now there are no invariants 
// for these written down, other than that the value of a Resource is unique and that the value
// must be represented in the ResourceSpace that it is allocated from.
//
// This whole section, might need to be revisited or removed in the future.

/// The values of a ResourceSpace must be unique within its type
/// TODO(Ilias) - Not sure that this is the right way of expressing this invariant, lets keep an
///               eye on whether it makes proofs a pain.
#[invariant]
pub open spec fn resource_space_value_unique(&self) -> bool {
    forall |s1: ResourceSpace, s2: ResourceSpace|
        self.spaces.contains(s1) && self.spaces.contains(s2) && s1 != s2  && s1.rtype() == s2.rtype() ==> s1.vals().disjoint(s2.vals())
}

/// The value of a Resource must be managed by the ResourceSpace that it is allocated from
#[invariant]
pub open spec fn resource_value_managed_by_space(&self) -> bool {
    forall |r: Resource, s: ResourceSpace| self.subsets.contains(SubsetEdge { src: r, dst: s }) ==> #[trigger] s.allocated_from(r)
}

// --------------------------------------- Resource Type Invariants -------------------------------

/// Subset edges must be between resources and resource spaces of the same type
#[invariant]
pub open spec fn subset_edge_type_consistent(&self) -> bool {
    forall |se: SubsetEdge| #[trigger] self.subsets.contains(se) ==> {
        &&& se.src().rtype() == se.dst().rtype()
    }
}

/// Map edges must not allow for physical resources to map to virtual resources
#[invariant]
pub open spec fn map_edge_type_consistent(&self) -> bool {
    forall |m: MapEdge| self.maps.contains(m) ==> {
        match m {
            MapEdge::SpaceBacking { sb_src, sb_dst } => sb_src.rtype() is Physical ==> sb_dst.rtype() is Physical,
            MapEdge::SpaceMap { sm_src, sm_dst } => sm_src.rtype() is Physical ==> sm_dst.rtype() is Physical,
            MapEdge::ResourceMap { rm_src, rm_dst } => rm_src.rtype() is Physical ==> rm_dst.rtype() is Physical
        }
    }
}

/// Map-Subset edge square invariant
/// This invariant states that if a Resource(x) maps to another Resource(y), and Space(x) and
/// Space(y) are the backing resource space for Resource(x) and Resource(y) respectively,
/// then there must exist a MapEdge from Space(x) to Space(y).
#[invariant]
pub open spec fn map_subset_edge_square(&self) -> bool {
    forall |me_res: MapEdge| self.maps.contains(me_res) && me_res is ResourceMap ==> {
        exists |se_src: SubsetEdge, se_dst: SubsetEdge, me_space: MapEdge| #![auto] {
            &&& self.subsets.contains(se_src)
            &&& self.subsets.contains(se_dst)
            &&& self.maps.contains(me_space)
            &&& me_space is SpaceMap
            // Resource(x) --SubsetEdge--> Space(x)
            &&& se_src.src() == me_res->rm_src
            // Space(x) --MapEdge--> Space(y)
            &&& me_space->sm_src == se_src.dst()
            // Space(y) --SubsetEdge--> Resource(y)
            &&& se_dst.src() == me_res->rm_dst
            &&& se_dst.dst() == me_space->sm_dst
        }
    }
}

/// Request edges must be directed to a domain which holds a space of the requested type
#[invariant]
pub open spec fn request_edge_type_consistent(&self) -> bool {
    forall |re: RequestEdge| #[trigger] self.requests.contains(re) ==> {
        exists |h: HoldEdge| {
            &&& self.holds.contains(h)
            &&& #[trigger] h.src() == re.dst()
            &&& h.dst() is Space
            &&& h.dst()->space.rtype() == re.rtype()
        }
    }
}

// Note:
// I haven't added the following invariants, from the previous version of the model as I'm not sure
// that they're necessary or useful, but they can be added back if needed:
// - spaces are mapped either to resources or other spaces

// --------------------------------- Initial State ------------------------------------------------

/// The initial state of the OSmosis model is a single running Protection Domain and a set of 
/// associated physical resource spaces.
init! {
    initialize(dom: ProtectionDomain, initial_spaces: Set<ResourceSpace>) {
        // All The initial ResourceSpaces are Physical
        require forall |rs| #[trigger] initial_spaces.contains(rs) ==> rs.rtype() is Physical;
        // The initial spaces must be a finite set
        require initial_spaces.finite();
        // The initial spaces must be disjoint if they're of the same type
        require forall |rs1, rs2| initial_spaces.contains(rs1) && initial_spaces.contains(rs2) && rs1 != rs2 && rs1.rtype() == rs2.rtype() ==> rs1.vals().disjoint(rs2.vals());

        init domains = Set::empty().insert(dom);
        init resources = Set::empty();
        init spaces = initial_spaces;
        init holds = initial_spaces.map(|s| HoldEdge { src: dom, dst: ResourceLike::Space { space: s } });
        init maps = Set::empty();
        init subsets = Set::empty();
        init requests = Set::empty();
    }
}
                
// --------------------------------------- Transition Rules ---------------------------------------
// All transitions take as a first argument the `act` ProtectionDomain, which is the domain that is
// performing this transition in the system. This is useful for checking relevant preconditions for
// each transition. For example in the create_protection_domain transition, we need to check that 
// the act PD holds the correct request edges to create the new PD and grant it the necessary 
// requests.

/// Creates a new Protection Domain in the system, which is an empty execution context, with a
/// set of request edges, these can be used to obtain resources for the new PD.
transition! {
    create_protection_domain(act: ProtectionDomain, new: ProtectionDomain, reqs: Set<RequestEdge>)
    {
        // act must exist
        require pre.domains.contains(act);
        // new must not exist
        require !pre.domains.contains(new);
        // reqs must be a finite set
        require reqs.finite();
        // the requests must be directed to the act PD and sourced from the new PD
        require forall |re: RequestEdge| #![auto] reqs.contains(re) ==> {
            &&& re.src() == new
            &&& re.dst() == act
        };
        // the requests must be of a type that the act PD holds
        require forall |re: RequestEdge| reqs.contains(re) ==> {
            exists |h: HoldEdge| #![auto] {
                &&& pre.holds.contains(h)
                &&& h.src() == act
                &&& h.dst() is Space
                &&& h.dst()->space.rtype() == re.rtype()
            }
        };

        update domains = pre.domains.insert(new);
        update requests = pre.requests.union(reqs);
    }
}
/// Creates a new Resource in the system, attaching it to the act Protection Domain, which holds
/// the resource space from which it's allocated. 
transition! {
    create_resource(act: ProtectionDomain, res: Resource)
    {
        // act must exist
        require pre.domains.contains(act);
        // res must not exist
        require !pre.resources.contains(res);
        // act must hold a resource space of the same type as res which contains the value of res
        require exists |h: HoldEdge| #![auto] {
            &&& pre.holds.contains(h)
            &&& h.src() == act
            &&& h.dst() is Space
            &&& h.dst()->space.rtype() == res.rtype()
            &&& h.dst()->space.allocated_from(res)
        };

        let space_hold_edge = choose |h: HoldEdge| #![auto] {
            &&& pre.holds.contains(h) 
            &&& h.src() == act 
            &&& h.dst() is Space 
            &&& h.dst()->space.rtype() == res.rtype() 
            &&& h.dst()->space.allocated_from(res)
        };
        let space = space_hold_edge.dst()->space;

        update resources = pre.resources.insert(res);
        update holds = pre.holds.insert(HoldEdge { src: act, dst: ResourceLike::Resource { res } });
        update subsets = pre.subsets.insert(SubsetEdge { src: res, dst: space });
    }
}

/// Grants a resource held by the `act` Protection Domain to the `pd` Protection Domain.
transition! {
    grant_resource(act: ProtectionDomain, pd: ProtectionDomain, res: Resource)
    {
        // act must exist
        require pre.domains.contains(act);
        // pd must exist
        require pre.domains.contains(pd);
        // res must exist and be held by act
        require pre.resources.contains(res);
        require pre.holds.contains(HoldEdge { src: act, dst: ResourceLike::Resource { res } });
        // A request edge must exist from pd to act for the resource type of res
        require exists |re: RequestEdge| #![auto] {
            &&& pre.requests.contains(re)
            &&& re.src() == pd
            &&& re.dst() == act
            &&& re.rtype() == res.rtype()
        };

        update holds = pre.holds.insert(HoldEdge { src: pd, dst: ResourceLike::Resource { res } });
    }
}

/// Revokes a resource held by the `act` Protection Domain, from the `pd` Protection Domain.
/// `act` must be holding the resource space from which the resource is allocated.
transition! {
    revoke_resource(act: ProtectionDomain, pd: ProtectionDomain, res: Resource)
    {
        // act must exist
        require pre.domains.contains(act);
        // pd must exist
        require pre.domains.contains(pd);
        // res must exist and be held by both act and pd
        require pre.resources.contains(res);
        require pre.holds.contains(HoldEdge { src: pd, dst: ResourceLike::Resource { res } });
        require pre.holds.contains(HoldEdge { src: act, dst: ResourceLike::Resource { res } });
        // act must hold the resource space from which the resource is allocated
        require exists |h: HoldEdge| #![auto] {
            &&& pre.holds.contains(h)
            &&& h.src() == act
            &&& h.dst() is Space
            &&& h.dst()->space.allocated_from(res)
        };

        update holds = pre.holds.remove(HoldEdge { src: pd, dst: ResourceLike::Resource { res } });
    }
}

transition! {
    delete_resource(act: ProtectionDomain, res: Resource)
    {
        // act must exist
        require pre.domains.contains(act);
        // res must exist and be held by act
        require pre.resources.contains(res);
        require pre.holds.contains(HoldEdge { src: act, dst: ResourceLike::Resource { res } });
        // act must hold the resource space from which the resource is allocated
        require exists |h: HoldEdge| #![auto] {
            &&& pre.holds.contains(h)
            &&& h.src() == act
            &&& h.dst() is Space
            &&& h.dst()->space.allocated_from(res)
        };
        // There must not exist any hold edges to the resource other than the one from act
        require forall |h: HoldEdge| pre.holds.contains(h) && h.dst() == ResourceLike::Resource { res } ==> h.src() == act;
        // The resource must not be mapped or being used to map
        require pre.resource_is_unmapped(res);

        let space_hold_edge = choose |h: HoldEdge| #![auto] {
            &&& pre.holds.contains(h) 
            &&& h.src() == act 
            &&& h.dst() is Space 
            &&& h.dst()->space.allocated_from(res)
        };
        let space = space_hold_edge.dst()->space;
        let res_hold_edge = HoldEdge { src: act, dst: ResourceLike::Resource { res } };
        let res_subset_edge = SubsetEdge { src: res, dst: space };


        update resources = pre.resources.remove(res);
        update holds = pre.holds.remove(res_hold_edge);
        update subsets = pre.subsets.remove(res_subset_edge);
    }
}



// -------------------------------------- Inductive Proofs ----------------------------------------

#[inductive(initialize)]
fn initialize_inductive(post: Self, dom: ProtectionDomain, initial_spaces: Set<ResourceSpace>) { 
    let map_fn = |s: ResourceSpace| HoldEdge { src: dom, dst: ResourceLike::Space { space: s } };

    use crate::utils::set_map_finite_preserving;

    // Invariant: holds_is_finite
    assert(post.holds_is_finite()) by {
        set_map_finite_preserving(initial_spaces, map_fn);
    }

    // Invariant: all_spaces_are_held
    assert forall |s: ResourceSpace| post.spaces.contains(s) implies 
        exists |h: HoldEdge| #[trigger] post.holds.contains(h) && h.dst() == ResourceLike::Space { space: s } by {
            let he = map_fn(s);
            assert(post.holds.contains(he) && he.dst() == ResourceLike::Space { space: s });
    }
}

#[inductive(create_protection_domain)]
fn create_protection_domain_inductive(pre: Self, post: Self, act: ProtectionDomain, new: ProtectionDomain, reqs: Set<RequestEdge>) { }

#[inductive(create_resource)]
fn create_resource_inductive(pre: Self, post: Self, act: ProtectionDomain, res: Resource) {
    let space_hold_edge = choose |h: HoldEdge| #![auto] {
        &&& pre.holds.contains(h) 
        &&& h.src() == act 
        &&& h.dst() is Space 
        &&& h.dst()->space.rtype() == res.rtype() 
        &&& h.dst()->space.allocated_from(res)
    };
    let space = space_hold_edge.dst()->space;    
    let new_subset_edge = SubsetEdge { src: res, dst: space };

    // Invariant: all_resources_are_held
    assert forall |r: Resource| post.resources.contains(r) implies
        exists |h: HoldEdge| #[trigger] post.holds.contains(h) && h.dst() == ResourceLike::Resource { res: r } by {
            let h = if (r == res) {
                HoldEdge { src: act, dst: ResourceLike::Resource { res } }
            } else {
                choose |h| #[trigger] pre.holds.contains(h) && h.dst() == ResourceLike::Resource { res: r }
            };
            assert(post.holds.contains(h) && h.dst() == ResourceLike::Resource { res: r });
        }

    // Invariant: all_resources_subset_spaces
    assert forall |r: Resource| post.resources.contains(r) implies
        exists |se: SubsetEdge| post.subsets.contains(se) && #[trigger] se.src() == r by {
            let se = if (r == res) {
                SubsetEdge { src: res, dst: space }
            } else {
                choose |se| pre.subsets.contains(se) && #[trigger] se.src() == r
            };
            assert(post.subsets.contains(se) && se.src() == r);
        }
}

#[inductive(grant_resource)]
fn grant_resource_inductive(pre: Self, post: Self, act: ProtectionDomain, pd: ProtectionDomain, res: Resource) { }

#[inductive(revoke_resource)]
fn revoke_resource_inductive(pre: Self, post: Self, act: ProtectionDomain, pd: ProtectionDomain, res: Resource) { }

#[inductive(delete_resource)]
fn delete_resource_inductive(pre: Self, post: Self, act: ProtectionDomain, res: Resource) { }


// ----------------------------------- Helper Spec  Functions -------------------------------------

/// Returns true if the give resource is not contained in  any of the graph's map edges.
pub open spec fn resource_is_unmapped(&self, res: Resource) -> bool {
    forall |m| self.maps.contains(m) ==> match m {
        MapEdge::SpaceBacking { sb_src, sb_dst } => sb_dst != res,
        MapEdge::SpaceMap { sm_src, sm_dst } => true,
        MapEdge::ResourceMap { rm_src, rm_dst } => rm_src != res && rm_dst != res,
    }
}


} // osmosis
} // state_machine!

// --------------------------------------- Node Types ---------------------------------------------

/// Protection Domain (PD) - An execution context, such as a process, tread, container or virtual machine.
pub ghost struct ProtectionDomain {
    /// The unique identifier of the Protection Domain
    pub id: nat,
}

impl ProtectionDomain {

    /// Creates a new Protection Domain with the given id.
    pub closed spec fn new(id: nat) -> ProtectionDomain {
        ProtectionDomain { id }
    }

    /// Obtains the id of a Protection Domain
    pub open spec fn id(&self) -> nat {
        self.id
    }
}

/// Resource - A passive entity, such as a virtual memory page, DRAM page, or a file.
pub ghost struct Resource {
    /// The type of the Resource, which can be either Virtual or Physical
    pub rtype: ResourceType,
    /// The identifying value of the Resource, which is unique within its type
    pub val: nat,
}

impl Resource {
    /// Obtains the type of the Resource
    pub open spec fn rtype(&self) -> ResourceType {
        self.rtype
    }

    /// Obtains the identifying value of the Resource
    pub open spec fn val(&self) -> nat {
        self.val
    }
}

/// Resource Space - A pool for resource allocations, such as a virtual address space, DRAM pages, cgroups, or a Cspace.
pub ghost struct ResourceSpace {
    /// The type of the ResourceSpace
    pub rtype: ResourceType,
    /// The identifying values of the ResourceSpace, i.e. an abstraction of the set of resources being managed.
    pub vals: Set<nat>,
}

impl ResourceSpace {
    /// Obtains the type of the ResourceSpace
    pub open spec fn rtype(&self) -> ResourceType {
        self.rtype
    }

    /// Obtains the identifying values of the ResourceSpace
    pub open spec fn vals(&self) -> Set<nat> {
        self.vals
    }

    /// Determines if a Resource is allocated from this ResourceSpace
    pub open spec fn allocated_from(&self, res: Resource) -> bool {
        self.rtype() == res.rtype() && self.vals().contains(res.val())
    }
}

// ------------------------------------------ Edge Types ---------------------------------------

/// Hold edge - Indicates that a PD holds some set of rights over a Resource, or Resource Space.
pub ghost struct HoldEdge {
    /// The Protection Domain that holds the rights
    pub src: ProtectionDomain,
    /// The Resource or Resource Space that is held
    pub dst: ResourceLike,
}

impl HoldEdge {
    /// Returns the Protection Domain that holds the rights
    pub open spec fn src(&self) -> ProtectionDomain {
        self.src
    }

    /// Returns the Resource or Resource Space that is held
    pub open spec fn dst(&self) -> ResourceLike {
        self.dst
    }
}

/// Map edge - Indicates a mapping relationship between resources or spaces.
pub ghost enum MapEdge {
    /// Indicates that this resource is the backing for a resource space, such as a page of virtual 
    /// memory being used to back the address space of some process, i.e. storing the metadata for
    /// the allocations.
    /// 
    /// TODO(Ilias): I'm not sure that this kind of edge is actually necessary, it doesn't seem to
    ///              help in capturing mapping relationships, i.e. talking about the backing of a
    ///              mapping (like the page table for a virtual memory mapping) and I'm not sure
    ///              that we need it.
    SpaceBacking { sb_src: ResourceSpace, sb_dst: Resource },
    /// Indicates that the resources allocated by the source ResourceSpace are mapped to the
    /// resources allocated by the destination ResourceSpace, such as a virtual to physical memory
    /// mapping.
    SpaceMap { sm_src: ResourceSpace, sm_dst: ResourceSpace },
    /// Indicates that the source Resource is mapped to the destination Resource, such as a virtual
    /// memory page being mapped to a physical memory page.
    ResourceMap { rm_src: Resource, rm_dst: Resource },
}

/// Subset edge
pub ghost struct SubsetEdge {
    pub src: Resource,
    pub dst: ResourceSpace,
}

impl SubsetEdge {
    pub open spec fn src(&self) -> Resource {
        self.src
    }

    pub open spec fn dst(&self) -> ResourceSpace {
        self.dst
    }
}

/// Request edge
pub ghost struct RequestEdge {
    pub src: ProtectionDomain,
    pub dst: ProtectionDomain,
    pub rtype: ResourceType,
}

impl RequestEdge {
    pub open spec fn src(&self) -> ProtectionDomain {
        self.src
    }

    pub open spec fn dst(&self) -> ProtectionDomain {
        self.dst
    }

    pub open spec fn rtype(&self) -> ResourceType {
        self.rtype
    }
}

// --------------------------------------- Utility Types ---------------------------------------

/// Resource Type - Defines the type of a Resource or ResourceSpace
pub ghost enum ResourceType {
    /// Represents virtual hardware resources, such as virtual memory pages or virtual CPUs.
    Virtual(nat),
    /// Represents base line hardware resources, such as physical memory pages. This type is particularly useful
    /// for denotating the base types of a resource, such as physical memory in the case of memory.
    Physical(nat),
}

/// ResourceLike - A type that can be either a Resource or a ResourceSpace, used to abstract over both types.
/// This is useful for edges that can point to either type, such as HoldEdge or MapEdge.
pub ghost enum ResourceLike {
    Resource { res: Resource },
    Space { space: ResourceSpace },
}

impl ResourceLike {
    /// Obtains the type of the ResourceLike
    pub open spec fn rtype(&self) -> ResourceType {
        match self {
            ResourceLike::Resource { res } => res.rtype(),
            ResourceLike::Space { space } => space.rtype(),
        }
    }
}

} // verus!
