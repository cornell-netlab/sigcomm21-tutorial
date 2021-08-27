open Coq_minip4.Syntax

module Trivial = struct
  let prog1 = [], Nop
end

module Symbex = struct

  let prog1 = 
    
    let defns = 
      [VarDecl(Bit(8), "x", Bits (Util.repeat false 8))] in
    
    let cmd = 
      Seq(Extr("x"),
          If(Var("x"), 
             Seq(Assign("x", Bits([false;true;false;true;false;true;false;true])),
                 Seq(Emit("x"),
                     Seq(Assign("x", Bits(Util.repeat true 8)),
                         Emit("x")))),
             Emit("x"))) in 
    (defns, cmd)
end

module Vcgen = struct
  let prog1 = 
    let defns = 
      [VarDecl(Bit(8), "x", Bits (Util.repeat false 8))] in
    
    let cmd = 
      Seq(Extr("x"),
          Seq(If(Var("x"), 
                 Seq(Assign("x", Bits([false;true;false;true;false;true;false;true])),
                     Seq(Emit("x"),
                         Seq(Assign("x", Bits(Util.repeat true 8)),
                             Emit("x")))),
                 Emit("x")),
               Assert(Var("x")))) in 
    (defns, cmd)
end

module ACL = struct
  let prog = Coq_minip4.ACL.acl
  let rules = ["route", [{ rule_match = VBits(Util.repeat true 8);
                          rule_action = 0 }];
               "acl", [{ rule_match = VPair(VBits(Util.repeat true 8),
                                           VBits(Util.repeat false 8));
                        rule_action = 1 }] ]
end
