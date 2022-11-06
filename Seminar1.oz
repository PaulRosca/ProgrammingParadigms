% Exdrcise 1, Absolute function
{Browse 'Exercise 1, Absolute values'}
declare
fun {Abs X}
  {Number.abs X}
end
{Browse {VirtualString.toAtom 'ABS -10 = '#{Abs ~10}}}
{Browse {VirtualString.toAtom 'ABS -5.5 = '#{Abs ~5.5}}}
{Browse {VirtualString.toAtom 'ABS 0 = '#{Abs 0}}}
{Browse {VirtualString.toAtom 'ABS -99999 = '#{Abs ~99999}}}

% Exercise 2
{Browse 'Exercise 2, n^m'}
declare
fun {Pow N M}
   if M == 0 then
      1
   else
      N*{Pow N (M-1)}
   end
end
{Browse {VirtualString.toAtom '5^3 = '#{Pow 5 3}}}
{Browse {VirtualString.toAtom '3^0 = '#{Pow 3 0}}}
{Browse {VirtualString.toAtom '12^1 = '#{Pow 12 1}}}
{Browse {VirtualString.toAtom '3^3 = '#{Pow 3 3}}}

%Exercise 3
{Browse 'Exercise 3, Max(n,m) recursive'}
declare
fun {Max N M}
   if N == 0 then
      M
   else
      if M == 0 then
         N
      else
         1+{Max (N-1) (M-1)}
      end
   end
end
{Browse {VirtualString.toAtom 'Max(5,3) = '#{Max 5 3}}}
{Browse {VirtualString.toAtom 'Max(125,124) = '#{Max 125 124}}}
{Browse {VirtualString.toAtom 'Max(2,55) = '#{Max 2 55}}}
{Browse {VirtualString.toAtom 'Max(0,233) = '#{Max 0 233}}}
