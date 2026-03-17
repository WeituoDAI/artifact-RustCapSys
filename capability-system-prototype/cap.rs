use vstd::prelude::*;
use verus_state_machines_macros::tokenized_state_machine;

verus!{


#[derive(Structural, PartialEq, Copy, Clone)]
pub struct Id{
    inner : u64,
}
impl Id{
    pub closed spec fn val(self) -> u64{
        self.inner
    }
    pub closed spec fn new(val:u64) -> Self{
        Self { inner : val } 
    }
    pub proof fn lemma_new(val:u64)
        ensures Self::new(val).val() == val,
    {}
}


#[derive(Structural, PartialEq, Copy, Clone)]
pub enum Right{
    TAKE,
    GRANT,
    OTHER,
    FULL,
}
impl Right{
    #[verifier::when_used_as_spec(has_take_spec)]
    pub fn has_take(&self) -> (res:bool)
        ensures
            res == self.has_take()
    {
        match self {
            Right::TAKE => true,
            Right::FULL => true,
            _ => false
        }
    }

    pub open spec fn has_take_spec(&self) -> bool{
        match self {
            Right::TAKE => true,
            Right::FULL => true,
            _ => false
        }
    }

    #[verifier::when_used_as_spec(has_grant_spec)]
    pub fn has_grant(&self) -> (res:bool)
        ensures
            res == self.has_grant()
    {
        match self {
            Right::GRANT => true,
            Right::FULL => true,
            _ => false
        }
    }

    pub open spec fn has_grant_spec(&self) -> bool{
        match self {
            Right::GRANT => true,
            Right::FULL => true,
            _ => false
        }
    }
}

pub struct Cap{
    s : Id,
    t : Id,
    right : Right,
}

impl Cap{
    pub closed spec fn s(self) -> Id{
        self.s
    }

    pub closed spec fn t(self) -> Id{
        self.t
    }

    pub closed spec fn right(self) -> Right{
        self.right
    }

    #[verifier::when_used_as_spec(has_take_spec)]
    pub fn has_take(&self) -> (res:bool)
        ensures
            res == self.right().has_take(),
            res == self.has_take(),
    {
        self.right.has_take()
    }

    pub open spec fn has_take_spec(&self) -> bool{
        self.right().has_take()
    }

    #[verifier::when_used_as_spec(has_grant_spec)]
    pub fn has_grant(&self) -> (res:bool)
        ensures
            res == self.right().has_grant(),
            res == self.has_grant(),
    {
        self.right.has_grant()
    }

    pub open spec fn has_grant_spec(&self) -> bool{
        self.right().has_grant()
    }

    pub closed spec fn new(s:Id, t:Id, right:Right) -> Self{
        Self{
            s, t, right
        }
    }

    pub proof fn lemma_new(s:Id, t:Id, right:Right)
        ensures
            Self::new(s, t, right).s() == s,
            Self::new(s, t, right).t() == t,
            Self::new(s, t, right).right() == right,
    {}
}



////// tokenized state machine

tokenized_state_machine!{CapSystem {

fields{
    #[sharding(set)]
    pub objs : Set<Id>,

    #[sharding(multiset)]
    pub caps : Multiset<Cap>,

    #[sharding(variable)]
    pub max_id : u64,
}

#[invariant]
pub fn wf(&self) -> bool{
    &&& forall |cap:Cap| #[trigger]self.caps.contains(cap) ==>
            self.objs.contains(cap.s())
    &&& forall |cap:Cap| #[trigger]self.caps.contains(cap) ==>
            self.objs.contains(cap.t())    
}

#[invariant]
pub fn wf_id(&self) -> bool{
    // self.id_usable.disjoint(self.objs)
    forall |id:Id| #[trigger]self.objs.contains(id) ==>
        id.val() <= self.max_id
}

transition!{
    take(a:Id, b:Id, take:Cap, cap_to_take:Cap){
        have objs >= set { a };
        have objs >= set { b };
        require(a != b);
        have caps >= { take };
        have caps >= { cap_to_take };
        require(take.s() == a);
        require(take.t() == b);
        require(take.has_take());
        require(cap_to_take.s() == b);
        let new_cap = Cap::new(a, cap_to_take.t(), cap_to_take.right());
        add caps += { new_cap };
    }
}

#[inductive(take)]
pub fn take_inductive(pre:Self, post:Self, a:Id, b:Id, take:Cap, cap_to_take:Cap){
    let new_cap = Cap::new(a, cap_to_take.t(), cap_to_take.right());
    Cap::lemma_new(a, cap_to_take.t(), cap_to_take.right());
    assert forall |cap:Cap| #[trigger]post.caps.contains(cap) implies
        post.objs.contains(cap.s())
        && post.objs.contains(cap.t()) by
    {
        if cap == new_cap {
            assert(pre.caps.contains(cap_to_take));
        }
        else {
            assert(pre.caps.contains(cap));
        }
    }
}

transition!{
    grant(a:Id, b:Id, grant:Cap, cap_to_grant:Cap){
        have objs >= set { a };
        have objs >= set { b };
        require(a != b);
        have caps >= { grant };
        have caps >= { cap_to_grant };
        require(grant.s() == a);
        require(grant.t() == b);
        require(grant.has_grant());
        require(cap_to_grant.s() == a);
        let new_cap = Cap::new(b, cap_to_grant.t(), cap_to_grant.right());
        add caps += { new_cap };
    }
}

#[inductive(grant)]
pub fn grant_inductive(pre:Self, post:Self, a:Id, b:Id, grant:Cap, cap_to_grant:Cap){
    let new_cap = Cap::new(b, cap_to_grant.t(), cap_to_grant.right());
    Cap::lemma_new(b, cap_to_grant.t(), cap_to_grant.right());
    assert forall |cap:Cap| #[trigger]post.caps.contains(cap) implies
        post.objs.contains(cap.s())
        && post.objs.contains(cap.t()) by
    {
        if cap == new_cap {
            assert(pre.caps.contains(cap_to_grant));
        }
        else {
            assert(pre.caps.contains(cap));
        }
    }
}

transition!{
    create(a:Id){

        have objs >= set { a };
        require(pre.max_id < u64::MAX);
        birds_eye let id = pre.max_id;
        let id2 = add(id, 1);
        update max_id = id2;

        let new_id = Id::new(id2);

        add objs += set { new_id };
        let new_cap = Cap::new(a, new_id, Right::FULL);
        add caps += { new_cap };

        assert(new_id.val() == pre.max_id + 1);
    }
}

#[inductive(create)]
pub fn create_inductive(pre:Self, post:Self, a:Id){
    let new_id = Id::new(add(pre.max_id, 1));
    let new_cap = Cap::new(a, new_id, Right::FULL);
    Cap::lemma_new(a, new_id, Right::FULL);
    assert(post.wf()) by {
        assert forall |cap:Cap| #[trigger]post.caps.contains(cap) implies
            post.objs.contains(cap.s())
            && post.objs.contains(cap.t()) by
        {
            if cap == new_cap {}
            else { assert(pre.caps.contains(cap)); }
        }
    }
    assert(post.wf_id()) by {}
}

}}


////// exec code




/// counter
use vstd::invariant::*;
use vstd::atomic::*;
use vstd::modes::*;
pub tracked struct GhostStuff {
    pub tracked perm: PermissionU64,
    pub tracked token: CapSystem::max_id,
}
impl GhostStuff{
    pub closed spec fn wf(self, inst: CapSystem::Instance, 
        cell: PAtomicU64
    ) -> bool {
        &&& self.perm@.patomic == cell.id()
        &&& self.token.instance_id() == inst.id()
        &&& self.perm@.value == self.token.value()
    }
}
pub struct InvPredicate {}
pub struct InvConstants{
    pub inst : Tracked<CapSystem::Instance>,
    pub gh_cell : Ghost< PAtomicU64 >,
}
impl InvariantPredicate<
    InvConstants,
    GhostStuff,
> for InvPredicate {
    open spec fn inv(c:InvConstants, st:GhostStuff) -> bool{
        st.wf(c.inst@, c.gh_cell@)
    }
}

pub struct MyCounter{
    cell : PAtomicU64,
    inst : Tracked<CapSystem::Instance>,
    inv : Tracked<AtomicInvariant<InvConstants, GhostStuff, InvPredicate>>,
}
impl MyCounter{
    pub closed spec fn wf(self) -> bool{
        &&& self.inv@.constant().inst == self.inst@
        &&& self.inv@.constant().gh_cell == self.cell
    }
}





use std::rc::Rc;

struct ObjInner; // opaque, for further use

pub struct Obj{
    id : Id,
    inner : ObjInner,
    ghost_id : Tracked<CapSystem::objs>,
    instance : Tracked<CapSystem::Instance>,
    counter : Rc<MyCounter>,
}

pub struct CapE{
    inner : Cap,
    ghost_cap : Tracked<CapSystem::caps>,
    instance : Tracked<CapSystem::Instance>,
}

impl CapE{
    pub closed spec fn wf(self) -> bool{
        &&& self.instance@.id() == self.ghost_cap@.instance_id()
        &&& self.inner == self.ghost_cap@.element()
    }
    pub closed spec fn instance_id(self) -> InstanceId{
        self.instance@.id()
    }
}

impl Obj{
    pub closed spec fn wf(self) -> bool{
        &&& self.instance@.id() == self.ghost_id@.instance_id()
        &&& self.id == self.ghost_id@.element()
        &&& self.instance@.id() == self.counter.inst@.id()
        &&& self.counter.wf()
    }
    pub closed spec fn instance_id(self) -> InstanceId{
        self.instance@.id()
    }
    pub closed spec fn id(self) -> Id{
        self.id
    }
}


//////////////////////////////
impl Obj{
    pub fn take(&self, other:&Obj, take:&CapE, cap_to_take:&CapE) 
        -> (res:Option<CapE>)
    requires 
        self.wf(),
        other.wf(),
        take.wf(),
        cap_to_take.wf(),
        self.instance_id() == other.instance_id(),
        self.instance_id() == take.instance_id(),
        self.instance_id() == cap_to_take.instance_id(),

        self.id() != other.id(),
    ensures
        match res {
            Some(res) => res.wf() && res.instance_id() == self.instance_id(),
            None => true,
        }
    {
        if take.inner.s == self.id && take.inner.t == other.id 
           && take.inner.has_take()
           && cap_to_take.inner.s == other.id 
        {
            let new_cap = Cap{ 
                s : self.id,
                t : cap_to_take.inner.t,
                right : cap_to_take.inner.right
            };

            let tracked tmp;
            proof{
                let tracked output = self.instance.borrow().take(
                    self.ghost_id@.element(),
                    other.ghost_id@.element(),
                    take.ghost_cap@.element(),
                    cap_to_take.ghost_cap@.element(),
                    self.ghost_id.borrow(),
                    other.ghost_id.borrow(),
                    take.ghost_cap.borrow(),
                    cap_to_take.ghost_cap.borrow(),
                );
                tmp = output;
                assert(new_cap == output.element());
            }

            return Some(
                CapE{
                    inner : new_cap,
                    ghost_cap : Tracked(tmp),
                    instance : self.instance.clone(),
                }
            )

        }
        else {
            None
        }
    }


    pub fn grant(&self, other:&Obj, grant:&CapE, cap_to_grant:&CapE) 
        -> (res:Option<CapE>)
    requires 
        self.wf(),
        other.wf(),
        grant.wf(),
        cap_to_grant.wf(),
        self.instance_id() == other.instance_id(),
        self.instance_id() == grant.instance_id(),
        self.instance_id() == cap_to_grant.instance_id(),

        self.id() != other.id(),
    ensures
        match res {
            Some(res) => res.wf() && res.instance_id() == self.instance_id(),
            None => true,
        }
    {
        if grant.inner.s == self.id && grant.inner.t == other.id 
           && grant.inner.has_grant()
           && cap_to_grant.inner.s == self.id 
        {
            let new_cap = Cap{ 
                s : other.id,
                t : cap_to_grant.inner.t,
                right : cap_to_grant.inner.right
            };

            let tracked tmp;
            proof{
                let tracked output = self.instance.borrow().grant(
                    self.ghost_id@.element(),
                    other.ghost_id@.element(),
                    grant.ghost_cap@.element(),
                    cap_to_grant.ghost_cap@.element(),
                    self.ghost_id.borrow(),
                    other.ghost_id.borrow(),
                    grant.ghost_cap.borrow(),
                    cap_to_grant.ghost_cap.borrow(),
                );
                tmp = output;
                assert(new_cap == output.element());
            }

            return Some(
                CapE{
                    inner : new_cap,
                    ghost_cap : Tracked(tmp),
                    instance : self.instance.clone(),
                }
            )
        }
        else {
            None
        }
    }


    pub fn create(&self) -> (res:Option<(Obj, CapE)>)
        requires
            self.wf(),
        ensures
            match res {
                Some((obj, cap)) => {
                    &&& obj.wf()
                    &&& cap.wf()
                    &&& obj.instance_id() == self.instance_id()
                    &&& cap.instance_id() == self.instance_id()
                },
                None => true,
            }
    {
        // check the counter
        let counter = &self.counter;
        let count : u64;
        open_atomic_invariant!(counter.inv.borrow() => g => {
            let tracked GhostStuff { perm: perm, token: token} = g;

            count = counter.cell.load(Tracked(&perm));

            proof { g = GhostStuff { perm, token}; }
        });
        if count >= u64::MAX {
            return None
        }

        let res : Result<u64, _>;
        let tracked tmp_obj = None;
        let tracked tmp_cap = None;

        open_atomic_invariant!(counter.inv.borrow() => g => {
            let tracked GhostStuff { perm: mut perm, token: mut token} = g;
            assert(token.value() == perm.value());
            res = counter.cell.compare_exchange(Tracked(&mut perm), count, count + 1);
            proof{
                if res is Ok{
                    // assert(count < u64::MAX);
                    // assert(res.unwrap() == count);
                    let tracked (obj, cap) = self.instance.borrow().create(
                        self.ghost_id@.element(),
                        self.ghost_id.borrow(),
                        &mut token
                    );
                    tmp_obj = Some(obj.get());
                    tmp_cap = Some(cap.get());
                    // assert(obj@.element().val() == res.unwrap() + 1)
                }
            }

            proof {
                g = GhostStuff { perm, token}; 
            }
        });
        if !res.is_ok(){
            return None;
        }

        let new_id = Id{ inner : res.unwrap() + 1 };

        let new_cap = Cap {
            s : self.id,
            t : new_id,
            right : Right::FULL,
        };
        Some(
            (Obj{
                id : new_id,
                inner : ObjInner,
                ghost_id : Tracked(tmp_obj.tracked_unwrap()),
                instance : self.instance.clone(),
                counter : self.counter.clone(),
            },
            CapE { 
                inner : new_cap,
                ghost_cap : Tracked(tmp_cap.tracked_unwrap()),
                instance : self.instance.clone(),
            })
        )
    }
}





}//verus