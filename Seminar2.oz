% Exercise 1
declare
% Function for calculating N * (N-1) * (N-2) * ... * M
fun {FactG N M}
   if N == M then
      if M == 0 then 1
      else M
      end
   else N*{FactG N-1 M}
   end
end
fun {Fact N} % Factorial of N
   {FactG N 0}
end
fun {Comb N K}
   {Fact N} div ({Fact K}*{Fact N-K})
end
{Browse {Comb 10 3}}
{Browse {Comb 10 0}}
{Browse {Comb 15 7}}

% 1.a
fun {CombA N K}
   if K == 0 then 1
   else {FactG N N-K+1} div {Fact K}
   end
end
{Browse {CombA 10 3}}
{Browse {CombA 10 0}}
{Browse {CombA 15 7}}

% 1.b
declare
fun {CombBHelper N I K R}
   if K == I then
      R * (N-I+1) div I
      else {CombBHelper N (I+1) K (R*(N-I+1) div I)}
   end
end
fun {CombB N K}
   if K == 0 then 1
      else {CombBHelper N 1 K 1}
   end
end
{Browse {CombB 10 3}}
{Browse {CombB 10 0}}
{Browse {CombB 15 7}}

% 2
declare
fun {ReverseImproved L1 LP}
   case L1
   of
      nil then LP
   [] H|T then {ReverseImproved T H|LP}
   end
end
{Browse {ReverseImproved ['paul' 'is' 'cool'] nil}}

% 3
declare
fun lazy {Filter L H}
   case L of
      nil then nil
   [] A|As then if (A mod H) == 0 then {Filter As H}
                else A|{Filter As H}
                end
   end
end
fun {Sieve L X Y}
   if Y =< 0 then nil
      else
      case L of
         nil then nil
      [] H|T then
         if H > X then
            H|{Sieve {Filter T H} X (Y-1)}
         else
            {Sieve {Filter T H} X Y}
         end
      end
   end
end
declare
fun lazy {Gen N}
   N|{Gen N+1}
end
fun {Prime X Y}
   {Sieve {Gen 2} X Y}
end
fun {GenAfter N}
   {Prime N 1}
end
{Browse {GenAfter 10}}
{Browse {GenAfter 20}}

% 4
declare
Root = nil
proc {Preorder R}
   if R \= nil then {Browse R.1}
      if R.2 \= nil then {Preorder R.2} end
      if R.3 \= nil then {Preorder R.3} end
   end
end
proc {Insert Root Value RootOut}
   case Root of
      nil then RootOut = node(Value nil nil)
   [] node(CurrentValue LeftSide RightSide) then
      if Value =< CurrentValue then NewTree in
         RootOut = node(CurrentValue NewTree RightSide)
         {Insert LeftSide Value NewTree}
      else NewTree in
         RootOut = node(CurrentValue LeftSide NewTree)
         {Insert RightSide Value NewTree}
      end
   end
end
fun {Smallest Root}
   if Root == nil then nil
   elseif Root.2 == nil then
      Root.1
   else
      {Smallest Root.2}
   end
end
fun {Biggest Root}
   if Root == nil then nil
   elseif Root.3 == nil then
      Root.1
   else
      {Biggest Root.3}
   end
end
proc {AndProc B1 B2 ?B}
   if B1 then
      B = B2
   else
      B = false
   end
end
proc {IsSortedBST Root B}
   if Root == nil then
      B = true
   elseif (Root.2 \= nil) andthen ({Biggest Root.2}  > Root.1) then
      B = false
   elseif (Root.3 \= nil) andthen ({Smallest Root.3} < Root.1) then
      B = false
   else
      local B1 B2 in
         {IsSortedBST Root.2 B1}
         {IsSortedBST Root.3 B2}
         {AndProc B1 B2 B}
      end
   end
end
local NR1 NR2 NR3 NR4 NR5 BR BST1 BST2 in
   {Insert Root 12 NR1}
   {Insert NR1 5 NR2}
   {Insert NR2 30 NR3}
   {Insert NR3 15 NR4}
   {Insert NR4 7 NR5}
   {Browse NR5}
   {Browse 'preorder'}
   {Preorder NR5}
   {Browse 'preorder'}
   {Browse {Smallest NR5}}
   {Browse {Biggest NR5}}
   {IsSortedBST NR5 BST1}
   {Browse BST1}
   BR = node(30 node(20 nil nil) node(45 node(15 nil nil) nil))
   {IsSortedBST BR BST2}
   {Browse BST2}
end
