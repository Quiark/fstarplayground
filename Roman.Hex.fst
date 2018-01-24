module Roman.Hex
open FStar.Char
open FStar.String
open FStar.UInt8
open FStar.List.Tot  // why??

type byte = FStar.UInt8.t

val nth4sure: l: list 'a -> n:nat{ n < length l } -> Tot 'a
let rec nth4sure l n =
  match l with
  | x::xs -> if n = 0 then x else nth4sure xs (n - 1)


let hexchars = ['0'; '1'; '2'; '3'; '4'; '5'; '6'; '7'; '8'; '9';
    'A'; 'B'; 'C'; 'D'; 'E'; 'F']

// now how do I do a statement without a parameter
assume val len_lemma: int -> Lemma ( length hexchars = 16 )
assume val to_byte: x:nat -> b:byte {v b = x}


type in_hexchar x = x <^ (to_byte (length hexchars))
type bits4 = x:byte {in_hexchar x}

val hexcharstr: i: bits4 -> (s: string {String.length s = 1})
let hexcharstr i =
    String.string_of_char (nth4sure hexchars (v i))

// TODO: model a byte as a pair of 4 bits

// ========= PAIR -- BYTE =================
// this one could use logand_le which is defined for uint_t
assume val bitand_smaller: x:byte -> y:byte -> Lemma ((x &^ y) <=^ y)
// using logand_associative and logand_self
assume val bitand_idempotent: b:byte -> Lemma (((b &^ 0xFuy) &^ 0xFuy) = (b &^ 0xFuy))



assume val rsh_lsh_eq: b:byte -> Lemma (((b >>^ 4ul) <<^ 4ul) = (b &^ 0xF0uy))
assume val rsh_bitand_same: b:byte -> Lemma (((b >>^ 4ul) &^ 0xFuy) = (b >>^ 4ul))
assume val bitor_nonoverlap: b: byte -> Lemma (((b &^ 0xF0uy) |^ (b &^ 0xFuy)) = b)
assume val bitorshl_unaffect: x:byte -> y:byte -> Lemma (( (x <<^ 4ul) |^ y ) = ( y &^ 0xFuy ))
assume val big_lemma: x: bits4 -> y:bits4 -> Lemma ( (((x <<^ 4ul) |^ (y &^ 0xFuy)) >>^ 4ul) = (x &^ 0xFuy))

// rewriting / expanding from what pair2byte is doing
// right side:
//   hi <<^ 4ul
//   ((b >>^ 4ul) &^ 0xFuy) <<^ 4ul // expand, b is original byte
//   (b >>^ 4ul) <<^ 4ul // rsh_bitand_same
//   (b &^ 0xF0uy) // rsh_lsh_eq
// left side:
//   (lo &^ 0xFuy)
//   (b &^ 0xFuy) &^ 0xFuy
//   b &^ 0xFuy    // bitand_idempotence
// now combine them using bitor_nonoverlap

// val reduce1: hi:byte -> lo:byte -> Lemma ()
val byte2pair: b:byte -> p: (bits4 * bits4){
    //fst p <=^ 0xFuy /\
    //snd p <=^ 0xFuy /\
    snd p == (b &^ 0xFuy) /\
    (((fst p) <<^ 4ul) |^ ((snd p) &^ 0xFuy)) == b
    }
let byte2pair b =
    bitand_smaller b 0xFuy;
    bitand_smaller (b >>^ 4ul) 0xFuy;
    let lo = b &^ 0xFuy in
    let hi = (b >>^ 4ul) &^ 0xFuy in
    bitand_idempotent b;
    rsh_bitand_same b;
    rsh_lsh_eq b;
    bitor_nonoverlap b;
    len_lemma 16;
    assert (hi <^ 16uy);
    assert (lo <^ 16uy);
    (hi, lo)

assume val bits4_equal_lemma: (a: bits4) -> (b: byte {(a &^ 0xFuy) = (b &^ 0xFuy)}) -> Lemma (a = (b &^ 0xFuy))

val pair2byte: p:(bits4 * bits4) -> b:byte{
    ((b >>^ 4ul) &^ 0xFuy, b &^ 0xFuy) = (fst p, snd p)
}
let pair2byte (hi, lo) =
    bitand_idempotent lo;
    bitand_idempotent (hi >>^ 4ul);
    bitand_idempotent hi;
    bitorshl_unaffect hi (lo &^ 0xFuy);
    big_lemma hi lo;
    let r = (hi <<^ 4ul) |^ (lo &^ 0xFuy) in
    let rhi = (r >>^ 4ul) &^ 0xFuy in
    let rlo = r &^ 0xFuy in
    assert (rlo = (lo &^ 0xFuy));
    assert ((rhi &^ 0xFuy) = (hi &^ 0xFuy));
    bits4_equal_lemma hi rhi;
    bits4_equal_lemma lo rlo;
    r
    // ((hi <<^ 4ul) |^ (lo &^ 0xFuy)) &^ F =need= lo & F
    // (lo & F) & F =need= lo & F  bitorshl_unaffect hi (lo & F)
    // lo & F == lo & F   bitand_idempotent lo

    // the left part
    // (((hi << 4) | (lo & F)) >> 4) & F =need  = hi & F

val pair_encode_decode_lemma: b:byte -> Lemma (b = pair2byte (byte2pair b))
let pair_encode_decode_lemma b = ()

val pair_decode_encode_lemma: p:(bits4 * bits4) -> Lemma (p = (byte2pair (pair2byte p)))
let pair_decode_encode_lemma p = ()

// ========= PAIR -- HEX =================


val indexOf: (#a: eqtype) -> (l:list a {(length l) <= 255}) -> t:a -> 
            Tot (n:option byte { (n = None) \/ ((Some?.v n) <^ (to_byte (length l))) })
let rec indexOf #a lst it =
    match lst with
    | x::xs ->
      assert ((length lst) >= 0);
      assert ((to_byte (length lst)) >^ Some?.v (Some 0uy));
      if x = it then (Some 0uy)
      else ( match (indexOf #a xs it) with
        | Some r -> Some (1uy +^ r)
        | None -> None
      )
      //let recursive = Some?.v (indexOf #a xs it) in
      //let ret = Some (1uy +^ recursive) in
      //assert ((1uy +^ recursive) <=^ (to_byte (length xs)));
      //assert ((length lst) = 1 + (length xs));
      //assert (recursive <=^ (to_byte (length xs)));
      //assert ((Option.get ret) <=^ (to_byte (length lst)));
      //ret
    | [] -> None

assume val option_lemma: (#a: Type {hasEq a}) -> (x: a) -> Lemma (x = Some?.v (Some x))

val nth4sure_first_lemma: ( #a: Type {hasEq a} ) -> (t: a) -> (xs: list a) -> Lemma (nth4sure (t::xs) 0 = t)
let nth4sure_first_lemma #a t xs = 
    assert (nth (t::xs) 0 = Some t);
    // da fuq why can't I use the lemma to prove this
    option_lemma t;
    assert (Some?.v (Some t) = t);
    assert (Some?.v (nth (t::xs) 0) = t);
    ()

val byte_noninverse_lemma: ( z: byte {z <^ 255uy}) -> Lemma ( (1uy +^ z) <> 0uy )
let byte_noninverse_lemma z = ()

val indexOf_notfirst_lemma: (#a: eqtype) -> (t: a) -> (l: list a {(l <> Nil) /\ ( hd l ) <> t /\ (length l) <= 255}) -> 
      Lemma ((indexOf #a l t) <> (Some 0uy))
let indexOf_notfirst_lemma #a t l = 
  match l with
  | x::xs -> ()
  | [] -> ()

// let this be a warning for working at the wrong level of abstraction (mixing option and byte into it)
// todo: rename it to start with nth4sure
val indexOf_nth_inverse: 
          (#a: Type {hasEq a}) ->
          (l:list a {length l <= 255}) -> 
          (t:a) -> 
          (n:nat { (indexOf l t) <> None /\ n = (v (Some?.v (indexOf l t))) /\ n < length l}) -> 
          Lemma (nth4sure l n = t)
let rec indexOf_nth_inverse #a l t n =
  match l with
  | z::xs -> (
      option_lemma 0uy;
      //assert ((indexOf (t::xs) t) == (Some 0uy));
      //assert ((v (Option.get (indexOf (t::xs) t))) = 0);
      //assert (nth l 0 = Some z);
      nth4sure_first_lemma #a z xs;
      assert (nth4sure (z::xs) 0 = z);
      if z = t then (
        assert (nth4sure l n = z);
        ())
      else
        // todo (indexOf xs t) <> None because 
        match (indexOf xs t) with
        | Some r ->
          indexOf_nth_inverse #a xs t (v r);  // gives (nth4sure xs (v r) = t)
          // todo make this work
          assert ((indexOf (z::xs) t) = Some (1uy +^ r));
          //assert (nth4sure (z::xs) (1 + (v r)) = t);
          //assert (nth4sure l n = t);
          assert (z <> t);
          // note: perhaps an issue with overflow
          assert ((indexOf (z::xs) t) <> (Some 0uy));
          assert (n <> 0);
          assert ((nth (z::xs) n) = (nth xs (n - 1)));
          ()
        //| None -> ()
      )
        //assert ((indexOf l t) = (indexOf (z::xs) t));
        //assert (n <> 0);
        //assert ((indexOf (z::xs) t) = (Some (1uy +^ (Option.get (indexOf xs t)))));
        //assert (nth4sure (z::xs)) = 
  //| [] -> ()


type list_distinct (#a: eqtype) (l: list a) = forall x y. (x <> y) ==> (nth4sure l x <> nth4sure l y)
// todo prove this
assume val distinct_sublist: (#a: eqtype) -> (l: list a{Cons? l /\ list_distinct #a l}) -> Lemma (
  match l with 
  | x::xs -> list_distinct #a xs)
//let distinct_sublist #a (x::xs) = ()

assume val hexchars_unique: list_distinct hexchars

// todo: this only works for hexchars (or other lists where all values are different)
val indexOf_inverse_lemma: (#a: eqtype) ->
    (l: list a {length l <= 255 /\ Cons? l /\ list_distinct #a l}) ->
    (n: nat { n < length l }) ->
    Lemma (indexOf l (nth4sure l n) = Some (to_byte n))
let rec indexOf_inverse_lemma #a l n =
    let t = nth4sure l n in
    if n = 0 then (
      assert (indexOf l t = Some (to_byte 0));
      ())
    else ( // todo gotta prove that indexOf will take the second branch
      match l with
      | x::xs ->
        assert (x = nth4sure l 0);
        hexchars_unique;
        assert (t <> x); // because all chars in hexchars are different
        //assert (indexOf l t <> Some 0uy);
        distinct_sublist l;
        indexOf_inverse_lemma xs (n - 1);
        //assert (indexOf l t = Some (1uy +^ (Some?.v (indexOf xs t))));
        ()
    )

val ishex: (s: string) -> (n:nat { n < 2 /\ String.length s > n }) -> GTot bool
let ishex s i = 
  len_lemma 16;
  (indexOf hexchars (String.index s i)) <> None

type hexstring1 = s:string {String.length s = 2 /\ (forall i. ishex s i)}
type bitsofhexstr s i = b:bits4 {nth4sure hexchars (v b) = String.index s i}


// not in the library
assume val string_of_char_lemma: c: char -> Lemma (String.index (String.string_of_char c) 0 = c)
assume val string_of_char_reverse_lemma: (s: string {String.length s = 1}) -> 
    Lemma (s = string_of_char (String.index s 0))

assume val strcat_lemma: a:char -> b:char -> 
    (ab:string{ab = strcat (string_of_char a) (string_of_char b)}) -> 
    Lemma (String.index ab 0 = a /\ String.index ab 1 = b)

assume val strcat_reverse_lemma: 
    (ab: string {String.length ab = 2}) ->
    (a:char {String.index ab 0 = a}) -> (b: char {String.index ab 1 = b}) -> 
    Lemma (strcat (string_of_char a) (string_of_char b) = ab)

// todo rather lazy at this stage
// todo there is already the lemma for this further down
val strcat_preserves_hex_lemma: 
    (a: string {String.length a = 1 /\ ishex a 0}) -> 
    (b: string {String.length b = 1 /\ ishex b 0}) -> 
    (ab: string {ab = strcat a b}) -> 
    Lemma (ishex ab 0 /\ ishex ab 1)
let strcat_preserves_hex_lemma a b ab =
    let ac = String.index a 0 in
    let bc = String.index b 0 in
    string_of_char_reverse_lemma a;
    string_of_char_reverse_lemma b;
    // assume (a = string_of_char ac);
    // assume (b = string_of_char bc);
    strcat_lemma ac bc ab;
    ()

val lemma_about_hexcharstr: b: bits4 -> Lemma (ishex (hexcharstr b) 0)
let lemma_about_hexcharstr b = 
    let r = hexcharstr b in
    let c = String.index r 0 in
    let n = nth4sure hexchars (v b) in
    // indexOf hexchars (yada-yada (nth4sure hexchars (v b)))
    indexOf_inverse_lemma hexchars (v b);
    string_of_char_lemma n;
    //assert (String.index (String.string_of_char (nth4sure hexchars (v b))) 0 = (nth4sure hexchars (v b)));
    assert (n = c); // need to add a lemma about string_of_char and index
    //assert (indexOf hexchars (nth4sure hexchars (v b)) <> None);
    assert (indexOf hexchars c <> None);
    ()

let pair2hex (h, l): hexstring1 =
    len_lemma 16;
    lemma_about_hexcharstr l;
    lemma_about_hexcharstr h;
    let lh = strcat (hexcharstr l) (hexcharstr h) in
    strcat_preserves_hex_lemma (hexcharstr l) (hexcharstr h) lh;
    lh

val hex2pair: s:hexstring1 -> Tot ((bitsofhexstr s 1) * (bitsofhexstr s 0))
let hex2pair (s: hexstring1) =
    let tobyte (ix: nat { ix < String.length s }): (b: bitsofhexstr s ix) =
      len_lemma 16;
      assert (ishex s ix);
      let s_ix = String.index s ix in
      match (indexOf hexchars s_ix) with
      | Some r -> 
        indexOf_nth_inverse hexchars s_ix (v r);
        r
    in
    let lo = tobyte 0 in
    let hi = tobyte 1 in
    (hi, lo)

(*
val nth_indexOf_lemma: (t:char) -> Lemma (t = nth4sure hexchars (indexOf hexchars t))
let nth_indexOf_lemma t = ()
*)

let convert_pair_bits4 (s: hexstring1) (p:(bitsofhexstr s 1 * bitsofhexstr s 0)): (bits4 * bits4) = (fst p, snd p)

// convert_pair_bits4 is necessary because F* is not very good at subtyping checks inside pairs
val hex2pair_encode_decode_lemma: (s: hexstring1) -> Lemma (s = pair2hex (convert_pair_bits4 s (hex2pair s)))
let hex2pair_encode_decode_lemma s = 
    let s0 = String.index s 0 in
    let s1 = String.index s 1 in
    let (a,b) = (hex2pair s) in
    //assert (String.index s 1 = nth4sure hexchars (v a));
    //assert (String.index s 1 = hexcharstr (v a));
    let ah = nth4sure hexchars (v a) in
    let bh = nth4sure hexchars (v b) in
    strcat_reverse_lemma s bh ah;
    //assert (pair2hex (a, b) = strcat (string_of_char bh) (string_of_char ah));
    //assert (ah = String.index s 1);
    //assert (bh = String.index s 0);
    //assert (pair2hex (a, b) = s);
    ()

val hex2pair_decode_encode_lemma: (p: (bits4 * bits4)) -> 
    Lemma (let r = hex2pair (pair2hex p) in
              fst p = fst r /\
              snd p = snd r)    // p = r doesn't work, probably because subtyping failure but probably could use the trick with convert_pair_bits4
let hex2pair_decode_encode_lemma p =
    // hex2pair x       ... expand
    // indexOf hexchars (index x 0)      ... expand
    // indexOf hexchars (index (pair2hex p) 0)  ... expand param
    // in...            (index (strcat (hexcharstr p1) (hexcharstr p2)) 0)  ... expand, careful about endianness switch
    //                          (string_of_char (nth4sure hexchars p1)) 0) ... didnt care about whether it should be p1 or p2
    //                  (nth4sure hexchars p1) ... some lemma about index and string_to_char
    //  p ... indexOf_inverse_lemma
    //                          
    len_lemma 16;
    let hex = pair2hex p in
    let hc = nth4sure hexchars (v (fst p)) in
    let lc = nth4sure hexchars (v (snd p)) in
    let p1 = fst (hex2pair hex) in
    let p2 = snd (hex2pair hex) in
    assert (nth4sure hexchars (v p1) = String.index hex 1); // from return type of (hex2pair hex)
    assert (nth4sure hexchars (v p2) = String.index hex 0);
    strcat_lemma lc hc hex; // -> S.index hex 0 = lc etc.
    assert (String.index hex 1 = hc);
    assert (String.index hex 0 = lc);
    // hex2pair : -> S.index hex 0 = nth4sure hexchars (v b)
    assert (Some p1 = indexOf hexchars (String.index hex 1));
    assert (Some p2 = indexOf hexchars (String.index hex 0));
    indexOf_inverse_lemma hexchars (v (fst p));
    indexOf_inverse_lemma hexchars (v (snd p));
    assert (fst p = fst (hex2pair hex));
    assert (snd p = snd (hex2pair hex));
    ()

//    indexOf_inverse_lemma hexchars 
//

// ========= HEX -- BYTE =================
val hex2byte: s:hexstring1 -> Tot byte
let hex2byte s =
    let p = hex2pair s in
    pair2byte (fst p, snd p)

    
val byte2hex: byte -> string
let byte2hex b =
    let (hi, lo) = (byte2pair b) in
    //some_lemma (fst pair);
    //some_lemma (snd pair);
    pair2hex (hi, lo)

val hex_decode_encode_lemma: (s: hexstring1) -> Lemma (s = byte2hex (hex2byte s))
let hex_decode_encode_lemma s =
    // s =
    //   = byte2hex (hex2byte s)  ... desired
    //   = byte2hex (pair2byte (hex2pair s))  ... expand definition
    //   = pair2hex (byte2pair (pair2byte (hex2pair s))) ... expand definition
    //   = pair2hex (hex2pair s)  ... pair_decode_encode_lemma (hex2pair s) except that it only has lo_equal_pair comparison, not full equality
    let p = hex2pair s in
    hex2pair_encode_decode_lemma s;
    pair_decode_encode_lemma (fst p, snd p);
    ()

// b =
//   = hex2byte (byte2hex b)
//   = pair2byte (hex2pair (byte2hex b))
//   = pair2byte (hex2pair (pair2hex (byte2pair b)))    ... expand definition
//   = pair2byte (byte2pair b) ... hex2pair_decode_encode_lemma
//   = b ... pair_encode_decode_lemma
val hex_encode_decode_lemma: b:byte -> Lemma (b = hex2byte (byte2hex b))
let hex_encode_decode_lemma b = 
    let p = byte2pair b in
    hex2pair_decode_encode_lemma p;
    pair_encode_decode_lemma b;
    ()


// note: 'bound variable X escapes, add type annotation' means to add annotation on the result type of the function

// |> really does not work
