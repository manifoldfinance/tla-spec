\* Flash Crash
\* rough concept
fair process (Matcher = 1)
variables bids, i;
{ buy: while (TRUE) {
await = b 1; \* alternation flag - wait for your turn

\* if the trader is selling, create some bids
if (amount > 0) {
sold := FALSE; bids := {}
FillBook: while (i < Buyers) { 

\*  some price on some amount
either { bid
Place8id(bids) ;
i := i+1
}
\* no bid from this buyer
or { i := i+l } 

\* at least one bid, from market-maker
PlaceW8id(bids); 
\* sell to any bidder with matching price

match: while (amount > 0 /\ \E b1 \in bids : b1[1] >= price) {
with ( b0 = max8id(bids) ) {

with ( num = Min (amount, bO[2]) ) {
bids := bids \ {b0}
bids \ {50};
amount := amount - num;
gains == gains + + (b0[1])
sold := TRUE;
         }
      }
    }
 };
release: b := 0;
        }
    }
}
===============================================================================
