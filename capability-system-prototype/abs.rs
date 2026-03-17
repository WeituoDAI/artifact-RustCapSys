use vstd::prelude::*;
use verus_state_machines_macros::tokenized_state_machine;
use super::cap::*;

verus!{

use vstd::multiset::*;

pub ghost struct CapState{
    pub objs : Set<Id>,
    pub caps : Multiset<Cap>,
}

pub open spec fn interp(s:CapSystem::State) -> CapState{
    CapState{
        objs : s.objs,
        caps : s.caps,
    }
}

impl CapState{
    pub open spec fn next(pre:Self, post:Self) -> bool{
        ||| exists |i:Id, j:Id, take:Cap, cap_to_take:Cap| post == pre.take(i, j, take, cap_to_take)
        ||| exists |i:Id, j:Id, grant:Cap, cap_to_grant:Cap| post == pre.grant(i, j, grant, cap_to_grant)
        ||| exists |i:Id, j:Id| post == pre.create(i, j) 
    }

    pub open spec fn sane(self) -> bool{
        forall |cap:Cap| #[trigger]self.caps.contains(cap) ==>
            self.objs.contains(cap.s())
            && self.objs.contains(cap.t())
    }

    pub open spec fn take(self, i:Id, j:Id, take:Cap, cap_to_take:Cap) -> Self
    {
        if self.objs.contains(i) && self.objs.contains(j)
           && self.caps.contains(take) && self.caps.contains(cap_to_take)
           && take.has_take() && take.s() == i && take.t() == j 
           && cap_to_take.s() == j
        //    && cap_to_take != take
           && i != j
        {
            let new_cap = Cap::new(i, cap_to_take.t(), cap_to_take.right());
            // let caps = self.caps.remove(cap_to_take).insert(new_cap);
            let caps = self.caps.insert(new_cap);
            Self{
                objs : self.objs,
                caps : caps,
            }
        }
        else {
            self
        }
    }

    pub open spec fn grant(self, i:Id, j:Id, grant:Cap, cap_to_grant:Cap) -> Self
    {
        if self.objs.contains(i) && self.objs.contains(j)
           && self.caps.contains(grant) && self.caps.contains(cap_to_grant)
           && grant.has_grant() && grant.s() == i && grant.t() == j 
           && cap_to_grant.s() == i
        //    && cap_to_grant != grant
           && i != j
        {
            let new_cap = Cap::new(j, cap_to_grant.t(), cap_to_grant.right());
            // let caps = self.caps.remove(cap_to_grant).insert(new_cap);
            let caps = self.caps.insert(new_cap);
            Self{
                objs : self.objs,
                caps : caps,
            }
        }
        else {
            self
        }
    }

    pub open spec fn create(self, id:Id, new_id:Id) -> Self{
        if self.objs.contains(id) && !self.objs.contains(new_id){
            let new_cap = Cap::new(id, new_id, Right::FULL);
            Self{
                objs : self.objs.insert(new_id),
                caps : self.caps.insert(new_cap),
            }
        }
        else {
            self
        }
    }

    pub proof fn take_sane(self, x:Id, y:Id, take:Cap, cap_to_take:Cap)
        requires self.sane(),
        ensures self.take(x, y, take, cap_to_take).sane(),
    {
        if self.objs.contains(x) && self.objs.contains(y)
           && self.caps.contains(take) && self.caps.contains(cap_to_take)
           && take.has_take() && take.s() == x && take.t() == y
           && cap_to_take.s() == y
           && cap_to_take != take
           && x != y
        {
            let post = self.take(x, y, take, cap_to_take);
            let new_cap = Cap::new(x, cap_to_take.t(), cap_to_take.right());
            Cap::lemma_new(x, cap_to_take.t(), cap_to_take.right());
            assert forall |cap:Cap| #[trigger]post.caps.contains(cap) implies
                post.objs.contains(cap.s())
                && post.objs.contains(cap.t()) by
            {
                if cap == new_cap {
                    assert(self.caps.contains(cap_to_take));
                }
                else {
                    assert(self.caps.contains(cap));
                }
            }
        }
    }

    pub proof fn grant_sane(self, x:Id, y:Id, grant:Cap, cap_to_grant:Cap)
        requires self.sane(),
        ensures self.grant(x, y, grant, cap_to_grant).sane(),
    {
        if self.objs.contains(x) && self.objs.contains(y)
            && self.caps.contains(grant) && self.caps.contains(cap_to_grant)
            && grant.has_grant() && grant.s() == x && grant.t() == y
            && cap_to_grant.s() == x
            // && cap_to_grant != grant
            && x != y
        {
            let post = self.grant(x, y, grant, cap_to_grant);
            let new_cap = Cap::new(y, cap_to_grant.t(), cap_to_grant.right());
            Cap::lemma_new(y, cap_to_grant.t(), cap_to_grant.right());
            assert forall |cap:Cap| #[trigger]post.caps.contains(cap) implies
                post.objs.contains(cap.s())
                && post.objs.contains(cap.t()) by
            {
                if cap == new_cap {
                    assert(self.caps.contains(cap_to_grant));
                }
                else {
                    assert(self.caps.contains(cap));
                }
            }
        }
    } 

    pub proof fn create_sane(self, x:Id, y:Id)
        requires self.sane(),
        ensures self.create(x, y).sane(),
    {
        let new_cap = Cap::new(x, y, Right::FULL);
        Cap::lemma_new(x, y, Right::FULL);
        let post = self.create(x, y);
        assert forall |cap:Cap| #[trigger]post.caps.contains(cap) implies
            post.objs.contains(cap.s())
            && post.objs.contains(cap.t()) by
        {
            if cap == new_cap {}
            else {
                assert(self.caps.contains(cap));
            }
        }
    }
}


///  refinement
use verus_state_machines_macros::case_on_next;

proof fn interp_sane(s:CapSystem::State)
    requires
        s.invariant()
    ensures
        interp(s).sane(),
{}

proof fn refinement(pre:CapSystem::State, post:CapSystem::State)
    requires
        pre.invariant(),
        // post.invariant(),
        CapSystem::State::next(pre, post),
    ensures
        CapState::next(interp(pre), interp(post)),
{
    let s1 = interp(pre);
    let s2 = interp(post);

    case_on_next!{pre, post, CapSystem => {
        take(a, b, take, cap_to_take) => {
            assert(s2 == s1.take(a, b, take, cap_to_take));
        }
        grant(a, b, grant, cap_to_grant) => {
            assert(s2 == s1.grant(a, b, grant, cap_to_grant));
        }
        create(a) => {
            // assert(pre.max_id < u64::MAX);
            let new_id = Id::new(add(pre.max_id, 1));
            let new_cap = Cap::new(a, new_id, Right::FULL);
            Id::lemma_new(add(pre.max_id, 1));
            Cap::lemma_new(a, new_id, Right::FULL);
            // assert(new_id.val() == pre.max_id + 1);
            // assert(!s1.objs.contains(new_id));
            // assert(post.objs == pre.objs.insert(new_id));
            // assert(post.caps == pre.caps.insert(new_cap));
            assert(s2 == s1.create(a, new_id));
        }
    }}
}

}