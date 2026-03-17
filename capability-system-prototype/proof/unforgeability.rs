use vstd::prelude::*;
use crate::abs::*;
use crate::cap::*;
use super::common::*;

verus!{

impl CapState{
    pub open spec fn has_right_to(self, id:Id, right:Right) -> bool{
        exists|cap:Cap|
            #[trigger] self.caps.contains(cap) &&
            self.objs.contains(id) &&
            cap.t() == id && (cap.right() == right || cap.right() == Right::FULL)
    }
}

proof fn lemma_next_create(s:CapState, cmd:CreateCmd, id:Id, right:Right)
  requires
    s.sane(),
    legal_create(s, cmd),
    s.create(cmd.parent, cmd.child).has_right_to(id, right),
    s.objs.contains(id),
  ensures
    s.has_right_to(id, right),
{
    let s2 = s.create(cmd.parent, cmd.child);
    let cap = choose |cap:Cap| #[trigger] s2.caps.contains(cap) &&
            cap.t() == id && (cap.right() == right || cap.right() == Right::FULL);
    assert(s2.caps.contains(cap));
    assert(id != cmd.child);
    assert(cap.t() == id);
    let new_cap = Cap::new(cmd.parent, cmd.child, Right::FULL);
    Cap::lemma_new(cmd.parent, cmd.child, Right::FULL);
    assert(s2.caps == s.caps.insert(new_cap));
    if cap.s() != cmd.child {
        assert(s.caps.contains(cap));
    } else {}
}

proof fn lemma_next_grant(s:CapState, cmd:GrantCmd, id:Id, right:Right)
  requires
    s.sane(),
    legal_grant(s, cmd),
    s.grant(cmd.id, cmd.obj_to_grant, cmd.grant, cmd.cap_to_grant).has_right_to(id, right),
    s.objs.contains(id),
  ensures
    s.has_right_to(id, right),
{
    let s2 = s.grant(cmd.id, cmd.obj_to_grant, cmd.grant, cmd.cap_to_grant);
    let cap = choose |cap:Cap| #[trigger] s2.caps.contains(cap) &&
            cap.t() == id && (cap.right() == right || cap.right() == Right::FULL);
    let new_cap = Cap::new(cmd.obj_to_grant, cmd.cap_to_grant.t(), cmd.cap_to_grant.right());
    Cap::lemma_new(cmd.obj_to_grant, cmd.cap_to_grant.t(), cmd.cap_to_grant.right());
    assert(s2.caps == s.caps.insert(new_cap));
    if cap == new_cap {
        assert(s.caps.contains(cmd.cap_to_grant));
    }
    else {
        assert(s.caps.contains(cap));
    }
}

proof fn lemma_next_take(s:CapState, cmd:TakeCmd, id:Id, right:Right)
  requires
    s.sane(),
    legal_take(s, cmd),
    s.take(cmd.id, cmd.obj_to_take, cmd.take, cmd.cap_to_take).has_right_to(id, right),
    s.objs.contains(id),
  ensures
    s.has_right_to(id, right),
{
    let s2 = s.take(cmd.id, cmd.obj_to_take, cmd.take, cmd.cap_to_take);
    let cap = choose |cap:Cap| #[trigger] s2.caps.contains(cap) &&
            cap.t() == id && (cap.right() == right || cap.right() == Right::FULL);
    let new_cap = Cap::new(cmd.id, cmd.cap_to_take.t(), cmd.cap_to_take.right());
    Cap::lemma_new(cmd.id, cmd.cap_to_take.t(), cmd.cap_to_take.right());
    assert(s2.caps == s.caps.insert(new_cap));
    if cap == new_cap {
        assert(s.caps.contains(cmd.cap_to_take));
    }
    else {
        assert(s.caps.contains(cap));
    }
}

proof fn lemma_next_0(s:CapState, cmd:Cmd, id:Id, right:Right)
  requires
    s.sane(),
    s.objs.contains(id),
    s.step(cmd).has_right_to(id, right),
  ensures
    s.has_right_to(id, right)
{
    match cmd {
        Cmd::Create(cmd)=> if !legal_create(s, cmd) {}
                            else {lemma_next_create(s, cmd, id, right)},
        Cmd::Take(cmd)  => if !legal_take(s, cmd) {}
                            else {lemma_next_take(s, cmd, id, right)},
        Cmd::Grant(cmd) => if !legal_grant(s, cmd) {}
                            else {lemma_next_grant(s, cmd, id, right)}
      }
}


pub proof fn unforgeability(s:CapState, cmds:Seq<Cmd>, id:Id, right:Right)
  requires
    s.sane(),
    s.objs.contains(id),
    s.exec(cmds).has_right_to(id, right),
  ensures
    s.has_right_to(id, right)
  decreases
    cmds.len()
{
  if cmds.len() > 0 {
    let cmds1 = cmds.drop_last();
    let s2 = s.exec(cmds);
    let s1 = s.exec(cmds1);
    assert(s2 == s1.step(cmds.last()));
    assert(s1.sane()) by { preserve_sane(s, cmds1) }
    assert(s1.objs.contains(id)) by { lemma_dom(s, cmds1) }
    assert(s1.has_right_to(id, right)) by {
      lemma_next_0(s1, cmds.last(), id, right)
    }
    unforgeability(s, cmds.drop_last(), id, right);
  }
}

}