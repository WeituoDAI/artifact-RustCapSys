use vstd::prelude::*;
use crate::abs::*;
use crate::cap::*;
use super::common::*;

verus!{


// Connected
impl CapState{
    pub open spec fn leak(self, x:Id, y:Id) -> bool
    {
        &&& self.objs.contains(x)
        &&& self.objs.contains(y)
        &&& 
            exists |cap:Cap| (#[trigger]self.caps.contains(cap) &&
                cap.s() == x && cap.t() == y)
	}

    pub open spec fn edge(self, x:Id, y:Id) -> bool {
		self.leak(x, y) || self.leak(y, x)
	}

    pub open spec fn connected_i(self, x:Id, y:Id, n:nat) -> bool
        decreases n,
    {
        if (n == 0) { x == y && self.objs.contains(x) }
        else if (n == 1) { self.edge(x, y) }
        else{
            exists |z:Id| self.connected_i(x, z, (n-1) as nat) && self.edge(z, y)
        }
    }

    proof fn lemma_connected_i(self, x:Id, y:Id, z:Id, n : nat)
        requires self.edge(x, z) && self.connected_i(z, y, n)
        ensures self.connected_i(x, y, (n+1) as nat)
        decreases n
    {
        if(n==0){}
        else if (n == 1){
            assert(self.connected_i(x, z, 1) && self.edge(z, y));
        }
        else {
            let k = choose |k:Id| self.connected_i(z, k, (n-1) as nat) && self.edge(k, y);
            self.lemma_connected_i(x, k, z, (n-1) as nat);
            assert(self.connected_i(x, k, n));
        }
    }

    pub open spec fn connected(self, x:Id, y:Id) -> bool{
        exists |n : nat| self.connected_i(x, y, n)
    }


    pub proof fn edge_is_sym(self)
        ensures
            forall |x:Id, y:Id| self.edge(x, y) <==> self.edge(y, x)
    {}

    proof fn connected_i_is_sym(self, x:Id, y:Id, n : nat)
        requires self.connected_i(x, y, n)
        ensures self.connected_i(y, x, n)
        decreases n
    {
        if(n == 0){}
        else if(n == 1) {
                assert(self.edge(x, y));
                // edge_is_sym();
                assert(self.edge(y, x));
                assert(self.connected_i(y, x, 1));
        }
        else {
            let z = choose |z:Id| self.connected_i(x, z, (n-1) as nat) && self.edge(z, y);
            assert(self.edge(y, z));
            self.connected_i_is_sym(x, z, (n-1) as nat);
            assert(self.connected_i(z, x, (n-1) as nat));
            self.lemma_connected_i(y, x, z, (n-1) as nat);
            assert(self.connected_i(y, x, n))
        }
    }

    proof fn connected_i_is_trans(self, x:Id, y:Id, z:Id, n : nat, m:nat)
        requires self.connected_i(x, y, n) && self.connected_i(y, z, m)
        ensures self.connected_i(x, z, n+m)
        decreases n
    {
        if(n==0){}
        else if(n==1){self.lemma_connected_i(x, z, y, m)}
        else{
            let h = choose |h:Id| self.connected_i(x, h, (n-1) as nat) && self.edge(h, y);
            self.lemma_connected_i(h, z, y, m);
            self.connected_i_is_trans(x, h, z, (n-1) as nat, (m+1) as nat)
        }
    }

    pub broadcast proof fn connected_is_sym(self, x:Id, y:Id)
        requires #[trigger]self.connected(x, y)
        ensures self.connected(y, x)
    {
        let n = choose |n : nat| self.connected_i(x, y, n);
        self.connected_i_is_sym(x, y, n);
    }

    pub proof fn connected_is_trans(self, x:Id, y:Id, z:Id)
        requires self.connected(x, y) && self.connected(y, z)
        ensures self.connected(x, z)
    {
        let n = choose |n : nat| self.connected_i(x, y, n);
        let m = choose |n : nat| self.connected_i(y, z, n);
        self.connected_i_is_trans(x, y, z, n, m)
    }


    pub broadcast proof fn edge_to_connected(self, x : Id, y : Id)
        requires #[trigger]self.edge(x, y)
        ensures self.connected(x, y)
    {
        assert(self.connected_i(x, y, 1))
    }

  pub broadcast proof fn connected_is_ref(self, x:Id)
    requires self.objs.contains(x)
    ensures #[trigger] self.connected(x, x)
  {
    assert(self.connected_i(x, x, 0))
  }


  pub proof fn connected_i_contains(self, x:Id, y:Id, n:nat)
    requires self.connected_i(x, y, n)
    ensures self.objs.contains(x) && self.objs.contains(y)
    decreases n
  {
    if(n==0 || n==1) {}
    else {
      let z = choose |z : Id| self.connected_i(x, z, (n-1) as nat) && self.edge(z, y);
      self.connected_i_contains(x, z, (n-1) as nat)
    }
  }


}





impl CapState{

  pub proof fn lemma_take_edge(self, x:Id, y:Id, take:Cap, cap_to_take:Cap)
    requires
        self.sane(),
    ensures
        forall |p:Id, q:Id| #[trigger]self.take(x, y, take, cap_to_take).edge(p, q)
            ==> self.edge(p, q) 
                || p == x && q == cap_to_take.t()
                || q == x && p == cap_to_take.t()
  {
    assert forall |p:Id, q:Id| #[trigger]self.take(x, y, take, cap_to_take).edge(p, q)
      implies self.edge(p, q) 
            || p == x && q == cap_to_take.t()
            || q == x && p == cap_to_take.t()
    by {
        if self.objs.contains(x) && self.objs.contains(y)
           && self.caps.contains(take) && self.caps.contains(cap_to_take)
           && take.has_take() && take.s() == x && take.t() == y
           && cap_to_take.s() == y
           && cap_to_take != take
           && x != y
        {
            self.lemma_take_edge_0(x, y, take, cap_to_take, p, q)
        }
    }
  }

  proof fn lemma_take_edge_0(self, x:Id, y:Id, take:Cap, cap_to_take:Cap, p:Id, q:Id)
    requires
      self.objs.contains(x),
      self.objs.contains(y),
      take.has_take(),
      take.s() == x,
      take.t() == y,
      self.caps.contains(take),
      self.caps.contains(cap_to_take),
      cap_to_take.s() == y,
    //   cap_to_take != take,
      x != y,

      self.sane(),
      self.take(x, y, take, cap_to_take).edge(p, q)
    ensures
        self.edge(p, q)
        || p == x && q == cap_to_take.t()
        || q == x && p == cap_to_take.t()
  {
    let new_state = self.take(x, y, take, cap_to_take);
    let new_cap = Cap::new(x, cap_to_take.t(), cap_to_take.right());
    assert(new_state.caps == self.caps.insert(new_cap));
    Cap::lemma_new(x, cap_to_take.t(), cap_to_take.right());

    if p == x && q == cap_to_take.t() {}
    else if q == x && p == cap_to_take.t() {}
    else if new_state.leak(p, q) {
        let cap = choose |cap:Cap| (#[trigger]new_state.caps.contains(cap) &&
                cap.s() == p && cap.t() == q);

        assert(new_state.caps.contains(cap));
        assert(cap != new_cap);
        assert(self.caps.contains(cap));
        
    } else {
        let cap = choose |cap:Cap| (#[trigger]new_state.caps.contains(cap) &&
                cap.s() == q && cap.t() == p);
        assert(new_state.caps.contains(cap));
        assert(cap != new_cap);
        assert(self.caps.contains(cap));
    }
  }


  pub proof fn lemma_grant_edge(self, x:Id, y:Id, grant:Cap, cap_to_grant:Cap)
    requires
        self.sane(),
    ensures
        forall |p:Id, q:Id| #[trigger]self.grant(x, y, grant, cap_to_grant).edge(p, q)
            ==> self.edge(p, q) 
                || p == y && q == cap_to_grant.t()
                || q == y && p == cap_to_grant.t()
  {
        assert forall |p:Id, q:Id| #[trigger]self.grant(x, y, grant, cap_to_grant).edge(p, q)
            implies self.edge(p, q) 
                || p == y && q == cap_to_grant.t()
                || q == y && p == cap_to_grant.t()
        by {
            if self.objs.contains(x) && self.objs.contains(y)
                && self.caps.contains(grant) && self.caps.contains(cap_to_grant)
                && grant.has_grant() && grant.s() == x && grant.t() == y
                && cap_to_grant.s() == x
                // && cap_to_grant != grant
                && x != y
            {
                self.lemma_grant_edge_0(x, y, grant, cap_to_grant, p, q)
            }
        }
  }


  proof fn lemma_grant_edge_0(self, x:Id, y:Id, grant:Cap, cap_to_grant:Cap, p:Id, q:Id)
    requires
      self.objs.contains(x),
      self.objs.contains(y),
      grant.has_grant(),
      grant.s() == x,
      grant.t() == y,
      self.caps.contains(grant),
      self.caps.contains(cap_to_grant),
      cap_to_grant.s() == x,
    //   cap_to_grant != grant,
      x != y,

      self.sane(),
      self.grant(x, y, grant, cap_to_grant).edge(p, q)

    ensures
        self.edge(p, q)
        || p == y && q == cap_to_grant.t()
        || q == y && p == cap_to_grant.t()
  {
    let new_cap = Cap::new(y, cap_to_grant.t(), cap_to_grant.right());
    Cap::lemma_new(y, cap_to_grant.t(), cap_to_grant.right());
    let new_state = self.grant(x, y, grant, cap_to_grant);
    if p == y && q == cap_to_grant.t() {}
    else if q == y && p == cap_to_grant.t() {}
    else if new_state.leak(p, q){
        let cap = choose |cap:Cap| (#[trigger]new_state.caps.contains(cap) &&
                cap.s() == p && cap.t() == q);
        assert(self.caps.contains(cap));
    }
    else {
        let cap = choose |cap:Cap| (#[trigger]new_state.caps.contains(cap) &&
                cap.s() == q && cap.t() == p);
        assert(self.caps.contains(cap));
    }
  }

  proof fn lemma_create_edge_0(self, parent:Id, child:Id, p:Id, q:Id)
    requires
      self.create(parent, child).edge(p, q),
      self.sane(),
    ensures
      self.edge(p, q) || p == parent && q == child || p == child && q == parent
  {
    let new_cap = Cap::new(parent, child, Right::FULL);
    Cap::lemma_new(parent, child, Right::FULL);
    let new_state = self.create(parent, child);
    if p == parent && q == child {}
    else if p == child && q == parent {}
    else if new_state.leak(p, q) {
        let cap = choose |cap:Cap| (#[trigger]new_state.caps.contains(cap) &&
                cap.s() == p && cap.t() == q);
        assert(self.caps.contains(cap));
    }
    else {
        let cap = choose |cap:Cap| (#[trigger]new_state.caps.contains(cap) &&
                cap.s() == q && cap.t() == p);
        assert(self.caps.contains(cap));
    }
  }


  pub proof fn lemma_create_edge(self, parent:Id, child:Id)
    requires
      self.sane(),
    ensures
        forall |p:Id, q:Id| #[trigger]self.create(parent, child).edge(p, q)
        ==> self.edge(p, q) || p == parent && q == child || p == child && q == parent
  {
    assert forall |p:Id, q:Id| #[trigger]self.create(parent, child).edge(p, q)
      implies self.edge(p, q) || p == parent && q == child || p == child && q == parent
    by {
        self.lemma_create_edge_0(parent, child, p, q)
    }
  }
}


proof fn lemma_legal_grant(s:CapState, cmd:GrantCmd)
  requires legal_grant(s, cmd),
  ensures
    s.edge(cmd.id, cmd.obj_to_grant),
    s.edge(cmd.id, cmd.cap_to_grant.t()),
    s.connected(cmd.id, cmd.obj_to_grant),
    s.connected(cmd.id, cmd.cap_to_grant.t()),
    s.connected(cmd.obj_to_grant, cmd.cap_to_grant.t())
{
    broadcast use {CapState::edge_to_connected, CapState::connected_is_sym, CapState::connected_is_ref};
    assert(s.edge(cmd.id, cmd.obj_to_grant));
    assert(s.edge(cmd.id, cmd.cap_to_grant.t()));
    s.connected_is_trans(cmd.obj_to_grant, cmd.id, cmd.cap_to_grant.t());
}


proof fn lemma_legal_take(s:CapState, cmd:TakeCmd)
  requires legal_take(s, cmd),
  ensures
    s.edge(cmd.id, cmd.obj_to_take),
    s.edge(cmd.obj_to_take, cmd.cap_to_take.t()),
    s.connected(cmd.id, cmd.obj_to_take),
    s.connected(cmd.id, cmd.cap_to_take.t()),
    s.connected(cmd.obj_to_take, cmd.cap_to_take.t())
{
    broadcast use {CapState::edge_to_connected, CapState::connected_is_sym, CapState::connected_is_ref};
    assert(s.edge(cmd.id, cmd.obj_to_take));
    assert(s.edge(cmd.obj_to_take, cmd.cap_to_take.t()));
    s.connected_is_trans(cmd.id, cmd.obj_to_take, cmd.cap_to_take.t());
}


proof fn main_lemma_1(s:CapState, cmd:Cmd, p : Id , q:Id)
  requires
    s.sane(),
    s.objs.contains(p),
    s.objs.contains(q),
    s.step(cmd).edge(p, q),
  ensures
    s.connected(p, q)
{
  broadcast use {CapState::edge_to_connected, CapState::connected_is_sym, CapState::connected_is_ref};
  match cmd {
    Cmd::Grant(cmd) =>  {
      if legal_grant(s, cmd) {
        lemma_legal_grant(s, cmd);
        s.lemma_grant_edge(cmd.id, cmd.obj_to_grant, cmd.grant, cmd.cap_to_grant);
      }
    },
    Cmd::Take(cmd) => {
        if legal_take(s, cmd){
            lemma_legal_take(s, cmd);
            s.lemma_take_edge(cmd.id, cmd.obj_to_take, cmd.take, cmd.cap_to_take);
        }
    },
    Cmd::Create(cmd) => 
    {
        s.lemma_create_edge(cmd.parent, cmd.child);
    },
  }
}


proof fn main_lemma_2_0(s:CapState, cmd:Cmd, p:Id, q:Id, n:nat)
  requires
    s.sane(),
    !(cmd is Create),
    s.step(cmd).connected_i(p, q, n)
  ensures
    s.connected(p, q)
  decreases n
{
  let s2 = s.step(cmd);
  s2.connected_i_contains(p, q, n);
  assert(s2.objs.contains(p) && s2.objs.contains(q));
  assert(s.objs.contains(p) && s.objs.contains(q));
  if(n == 0) { s.connected_is_ref(p) }
  else if(n == 1) {
    assert(s.connected(p, q)) by {main_lemma_1(s, cmd, p, q)}
  }
  else {
    let z = choose |z : Id| s2.connected_i(p, z, (n-1) as nat) && s2.edge(z, q);
    assert(s.connected(p, z)) by { main_lemma_2_0(s, cmd, p, z, (n-1) as nat) }
    assert(s.connected(z, q)) by { main_lemma_1(s, cmd, z, q)}
    s.connected_is_trans(p, z, q)
  }
}


proof fn main_lemma_2(s:CapState, cmd:Cmd, p:Id, q:Id)
  requires
    s.sane(),
    !(cmd is Create),
    s.step(cmd).connected(p, q)
  ensures
    s.connected(p, q)
{
  let n = choose |n : nat| s.step(cmd).connected_i(p, q, n);
  main_lemma_2_0(s, cmd, p, q, n)
}


proof fn main_lemma_3_0(s:CapState, cmd:CreateCmd, p:Id, q:Id, n:nat)
  requires
    s.sane(),
    legal_create(s, cmd),
    s.create(cmd.parent, cmd.child).connected_i(p, q, n),
    s.objs.contains(p)
  ensures
    q == cmd.child ==> s.connected(p, cmd.parent),
    q != cmd.child ==> s.connected(p, q)
  decreases n
{
  broadcast use {CapState::edge_to_connected, CapState::connected_is_sym, CapState::connected_is_ref};

  if(n==0){}
  else if(n==1){ s.lemma_create_edge(cmd.parent, cmd.child) }
  else {
    let s2 = s.create(cmd.parent, cmd.child);
    let z = choose |z : Id| s2.connected_i(p, z, (n-1) as nat) && s2.edge(z, q);
    if(z == cmd.child){
      assert(s.connected(p, cmd.parent)) by {main_lemma_3_0(s, cmd, p, z, (n-1) as nat)}
      if(q == cmd.child){}
      else{
        assert(q == cmd.parent) by {s.lemma_create_edge(cmd.parent, cmd.child)}
      }
    }
    else{
      assert(s.connected(p, z)) by {main_lemma_3_0(s, cmd, p, z, (n-1) as nat)}
      if(q == cmd.child){
        assert(s.connected(z, cmd.parent)) by {main_lemma_3_0(s, cmd, z, q, 1)}
        assert(s.connected(p, cmd.parent)) by {s.connected_is_trans(p, z, cmd.parent)}
      } else {
        assert(s.connected(z, q)) by {main_lemma_3_0(s, cmd, z, q, 1)}
        assert(s.connected(p, q)) by {s.connected_is_trans(p, z, q)}
      }
    }
  }
}


proof fn main_lemma_3(s:CapState, cmd:CreateCmd, p:Id, q:Id)
  requires
    s.sane(),
    legal_create(s, cmd),
    s.create(cmd.parent, cmd.child).connected(p, q),
    s.objs.contains(p)
  ensures
    q == cmd.child ==> s.connected(p, cmd.parent),
    q != cmd.child ==> s.connected(p, q)
{
  let n = choose |n : nat| s.create(cmd.parent, cmd.child).connected_i(p, q, n);
  main_lemma_3_0(s, cmd, p, q, n)
}


proof fn main_lemma_connected(s:CapState, cmd:Cmd, p:Id, q:Id)
  requires
    s.sane(),
    s.step(cmd).connected(p, q),
    s.objs.contains(p),
    s.objs.contains(q)
  ensures
    s.connected(p, q)
{
  match cmd {
    Cmd::Create(cmd) => if !legal_create(s, cmd) {} else {main_lemma_3(s, cmd, p, q)},
    _ => main_lemma_2(s, cmd, p, q)
  }
}


pub proof fn isolation(s:CapState, cmds:Seq<Cmd>, x:Id, y:Id)
  requires
    s.sane(),
    s.objs.contains(x),
    s.objs.contains(y),
    s.exec(cmds).connected(x, y),
  ensures
    s.connected(x, y)
  decreases cmds.len()
{
  if cmds.len() > 0 {
    let cmds1 = cmds.drop_last();
    let s2 = s.exec(cmds);
    let s1 = s.exec(cmds1);
    assert(s2 == s1.step(cmds.last()));
    assert(s1.sane()) by { preserve_sane(s, cmds1) }
    assert(s1.objs.contains(x) && s1.objs.contains(y)) by {
      lemma_dom(s, cmds1);
    }
    assert(s1.connected(x, y)) by {
      main_lemma_connected(s1, cmds.last(), x, y)
    }
    isolation(s, cmds.drop_last(), x, y);
  }
}


}