use vstd::prelude::*;
use crate::abs::*;
use crate::cap::*;

verus!{


pub struct TakeCmd{
  pub id : Id,
  pub obj_to_take : Id,
  pub take : Cap,
  pub cap_to_take : Cap,
}

pub struct GrantCmd{
  pub id : Id,
  pub obj_to_grant : Id,
  pub grant : Cap,
  pub cap_to_grant : Cap,
}

pub struct CreateCmd{
  pub parent : Id,
  pub child : Id,
}

pub enum Cmd{
  Create(CreateCmd),
  Grant(GrantCmd),
  Take(TakeCmd)
}
impl CapState{
  pub open spec fn step(self, cmd:Cmd) -> Self{
      match cmd {
          Cmd::Create(cmd) => self.create(cmd.parent, cmd.child),
          Cmd::Grant(cmd) => self.grant(cmd.id, cmd.obj_to_grant, cmd.grant, cmd.cap_to_grant),
          Cmd::Take(cmd) => self.take(cmd.id, cmd.obj_to_take, cmd.take, cmd.cap_to_take),
      }
  }

  pub open spec fn exec(self, cmds:Seq<Cmd>) -> Self{
    cmds.fold_left(
      self,
      |s:Self, a:Cmd| s.step(a)
    )
  }
}

pub open spec fn legal_create(s:CapState, cmd:CreateCmd) -> bool{
  &&& s.objs.contains(cmd.parent)
  &&& !s.objs.contains(cmd.child)
}

pub open spec fn legal_take(s:CapState, cmd:TakeCmd) -> bool{
  &&& s.objs.contains(cmd.id)
  &&& s.objs.contains(cmd.obj_to_take)
  &&& s.caps.contains(cmd.take)
  &&& s.caps.contains(cmd.cap_to_take)
  &&& cmd.take.has_take()
  &&& cmd.take.s() == cmd.id
  &&& cmd.take.t() == cmd.obj_to_take
  &&& cmd.cap_to_take.s() == cmd.obj_to_take
  &&& cmd.id != cmd.obj_to_take
//   &&& cmd.cap_to_take != cmd.take
  &&& s.sane()
}

pub open spec fn legal_grant(s:CapState, cmd:GrantCmd) -> bool{
  &&& s.objs.contains(cmd.id)
  &&& s.objs.contains(cmd.obj_to_grant)
  &&& s.caps.contains(cmd.grant)
  &&& s.caps.contains(cmd.cap_to_grant)
  &&& cmd.grant.has_grant()
  &&& cmd.grant.s() == cmd.id
  &&& cmd.grant.t() == cmd.obj_to_grant
  &&& cmd.cap_to_grant.s() == cmd.id
  &&& cmd.id != cmd.obj_to_grant
//   &&& cmd.cap_to_grant != cmd.grant
  &&& s.sane()
}


pub proof fn preserve_sane_0(s:CapState, cmd:Cmd)
  requires
    s.sane(),
  ensures
    s.step(cmd).sane()
{
  match cmd {
      Cmd::Take(cmd) => { s.take_sane(cmd.id, cmd.obj_to_take, cmd.take, cmd.cap_to_take) },
      Cmd::Create(cmd) => { s.create_sane(cmd.parent, cmd.child) },
      Cmd::Grant(cmd) => { s.grant_sane(cmd.id, cmd.obj_to_grant, cmd.grant, cmd.cap_to_grant) }
  }
}

pub proof fn preserve_sane(s:CapState, cmds:Seq<Cmd>)
  requires
    s.sane(),
  ensures
    s.exec(cmds).sane()
  decreases cmds.len(),
{
  if cmds.len() > 0 {
    preserve_sane(s, cmds.drop_last());
    let s1 = s.exec(cmds.drop_last());
    preserve_sane_0(s1, cmds.last())
  }
}

pub proof fn lemma_dom_0(s:CapState, cmd:Cmd)
  ensures
    s.objs.subset_of(s.step(cmd).objs)
{}

pub proof fn lemma_dom(s:CapState, cmds:Seq<Cmd>)
  ensures
    s.objs.subset_of(s.exec(cmds).objs)
  decreases cmds.len()
{
  if cmds.len() > 0 {
    lemma_dom(s, cmds.drop_last());
    let s1 = s.exec(cmds.drop_last());
    lemma_dom_0(s1, cmds.last())
  }
}



}