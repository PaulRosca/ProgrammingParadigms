%1
declare
fun {Concat A1 A2}
   case A1 of
      nil then
      case A2 of
         nil then nil
      [] H|T then
         H|{Concat A1 T}
      [] H then
         H
      end
   [] H|T then
      H|{Concat T A2}
   [] H then
      H|{Concat nil A2}
   end
end

fun {ExtractFrom A E}
   case A of
      nil then nil
   [] H|T then
      if H == E then
         {ExtractFrom T E}
      else
         H|{ExtractFrom T E}
      end
   [] H then
      if H == E then
         nil
      else
         H
      end
   end
end
fun {FreeSet Expr}
   case Expr of
      nil then nil
   [] apply(E1 E2) then
      {Concat {FreeSet E1} {FreeSet E2}}
   [] let(I#E1 E2) then
      {ExtractFrom {Concat {FreeSet E1} {FreeSet E2}} I}
   [] lam(I E) then
      {ExtractFrom {FreeSet E} I}
   [] X then
      X
   end
end
{Browse {FreeSet apply(x let(x#y x))}}
{Browse {FreeSet apply(y apply(let(x#x x) y))}}

%2
declare
fun {IsMember E I}
   case E of
      nil then false
   [] H|T then
      case H of
         nil then false
      [] X#Y then
         if X == I then
            true
         else
            {IsMember T I}
         end
      end
   end
end
fun {Fetch E I}
   case E of
      nil then I
   [] H|T then
      case H of
         nil then I
      [] X#Y then
         if X == I then
            Y
         else
            {Fetch T I}
         end
      end
   end
end
fun {AdjoinHelper E X}
   case E of
      nil then nil
   [] H|T then
      case H of
         nil then nil
      [] A#B then
         if A == X then
         {AdjoinHelper T X}
         else
            H|{AdjoinHelper T X}
         end
      end
   end
end
fun {Adjoin E X#Y}
   X#Y|{AdjoinHelper E X}
end

{Browse {IsMember [a#e1 b#y c#e3] c}}
{Browse {IsMember [a#e1 b#y c#e3] y}}
{Browse {Fetch [a#e1 b#y c#e3] c}}
{Browse {Fetch [a#e1 b#y c#e3] d}}
{Browse {Adjoin [a#e1 b#y c#e3] c#e4}}
{Browse {Adjoin [a#e1 b#y c#e3] d#e4}}

%3
Cnt = {NewCell 0}
declare
fun {NewId}
   Cnt := @Cnt + 1
   {String.toAtom {Append "id<" {Append {Int.toString @Cnt} ">"}}}
end

fun {ReplaceWith Expr V ID}
   case Expr of
      nil then nil
   [] apply(E1 E2) then
      apply({ReplaceWith E1 V ID} {ReplaceWith E2 V ID})
   [] lam(I E) then
      if I == V then
         lam(ID {ReplaceWith E V ID})
      else
         lam(I {ReplaceWith E V ID})
      end
   [] let(I#E1 E2) then
      if I == V then
         let(ID#{ReplaceWith E1 V ID} {ReplaceWith E2 V ID})
      else
         let(I#{ReplaceWith E1 V ID} {ReplaceWith E2 V ID})
      end
   [] X then
      if X == V then
         ID
      else
         X
      end
   end
end

fun {Rename Expr}
   case Expr of
      nil then nil
   [] apply(E1 E2) then
      apply({Rename E1} {Rename E2})
   [] lam(I E) then ID in
      ID = {NewId}
      {ReplaceWith lam(ID {Rename E}) I ID}
   [] let(I#E1 E2) then ID in
      ID = {NewId}
      {ReplaceWith let(ID#{Rename E1} {Rename E2}) I ID}
   [] X then
      X
   end
end
{Browse {Rename lam(z lam(x z))}}
{Browse {Rename let(id#lam(z z) apply(id y))}}

%4
declare
fun {SubsHelper X#Y Expr}
   case Expr of
      nil then nil
   [] apply(E1 E2) then
      apply({SubsHelper X#Y E1} {SubsHelper X#Y E2})
   [] lam(I E) then
      if I == X then
         lam(Y {SubsHelper X#Y E})
      else
         lam(I {SubsHelper X#Y E})
      end
   [] let(I#E1 E2) then
      if I == X then
         let(Y#{SubsHelper X#Y E1} {SubsHelper X#Y E2})
      else
         let(I#{SubsHelper X#Y E1} {SubsHelper X#Y E2})
      end
   [] V then
      if V == X then
         Y
      else
         V
      end
   end
end

fun {Subs X#Y E}
   {SubsHelper X#Y {Rename E}}
end

{Browse {Subs x#lam(x x) apply(x y)}}
{Browse {Subs x#lam(z z) apply(x lam(x apply(x z)))}}
{Browse {Subs x#lam(y z) apply(x lam(z apply(x z)))}}
