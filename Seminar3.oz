% 1
declare
fun {Member Xs Y}
   case Xs of
      nil then false
   [] H|T then
      if H == Y then
         true
      else
         {Member T Y}
      end
   end
end
{Browse {Member [a b c] c}}
{Browse {Member [a b c] d}}

% 2
declare
fun {Take Xs N}
   if N == 0 then
      nil
   else
      case Xs of
         nil then nil
      [] H|T then
         H|{Take T (N-1)}
      end
   end
end
fun {Drop Xs N}
   if N == 0 then
      Xs
   else
      case Xs of
         nil then nil
      [] H|T then
         {Drop T (N-1)}
      end
   end
end
{Browse {Take [1 4 3 6 2] 3}}
{Browse {Drop [1 4 3 6 2] 3}}

% 3
declare
fun {Zip Pair}
   case Pair of
      nil then nil
   [] nil#nil then nil
   [] Xs#Ys then
      Xs.1#Ys.1|{Zip Xs.2#Ys.2}
   end
end
fun {UnzipFirst List}
   case List of
      nil then nil
   [] H|T then
      case H of
         nil then nil
      [] A#B then
         A|{UnzipFirst T}
      end
   end
end
fun {UnzipSecond List}
   case List of
      nil then nil
   [] H|T then
      case H of
         nil then nil
      [] A#B then
         B|{UnzipSecond T}
      end
   end
end
fun {Unzip List}
   {UnzipFirst List}#{UnzipSecond List}
end
Zipped = {Zip [a b c]#[1 2 3]}
{Browse Zipped}
{Browse {Unzip Zipped}}

% 4
declare
fun {Position Xs Y}
   if Xs.1 == Y then
      1
   else
      1+{Position Xs.2 Y}
   end
end
fun {PositionHelper Xs Y N}
   case Xs of
      nil then 0
   [] H|T then
      if H == Y then
         N
      else
         {PositionHelper T Y (N+1)}
      end
   end
end
fun {PositionImproved Xs Y}
   {PositionHelper Xs Y 1}
end
{Browse {Position [a b c] c}}
{Browse {PositionImproved [a b c] c}}
{Browse {PositionImproved [a b c] d}}

% 5
declare
fun {Eval Expr}
   case Expr of
      nil then nil
   [] int(N) then
      N
   [] add(X Y) then
      {Eval X}+{Eval Y}
   [] mull(X Y) then
      {Eval X}*{Eval Y}
   end
end
{Browse {Eval add(int(1) mull(int(3) int(4)))}}
