local

(*FOR TEMPORARY SYMBOL TABLE USED TO GENEARTE 3 AC CODE *)
datatype va = none | integer of int | boolean of bool | stri of string
datatype 'a TempST = empt | comb of 'a * va * string * 'a TempST
exception notemp

fun Name (comb(a,_,_,_)) = a
	| Name empt = raise notemp
fun Plac (comb(_,integer(b),_,_)) = Int.toString b
	| Plac (comb(_,boolean(b),c,_)) = Bool.toString b
	| Plac (comb(_,stri(b),c,_)) = b
	| Plac (comb(_,none,c,_)) = ""
	| Plac empt = raise notemp
fun Place (comb(_,a,_,_)) = a
	| Place empt = raise notemp
fun Rem (comb(_,_,_,c)) = c
	| Rem empt = raise notemp
fun Oper (comb(_,_,e,_)) = e
	| Oper empt = raise notemp

fun PlusComb x tst = comb(x,none,"",tst)
fun PlusPlace x y tst = 
	if (Name tst) = x then comb(x,y,(Oper tst),(Rem tst))
	else comb((Name tst),(Place tst),(Oper tst),(PlusPlace x y (Rem tst))) 
fun PlusOper x z tst = 
	if (Name tst) = x then comb(x,(Place tst),z,(Rem tst))
	else comb((Name tst),(Place tst),(Oper tst),(PlusOper x z (Rem tst)))	

fun findPlace x empt = ""
	| findPlace x tst =
		let
		in if (Name tst = x) then (Plac tst)
			 else findPlace x (Rem tst) 
		end

fun findValue x empt = none
	| findValue x tst =
		let
		in if (Name tst = x) then (Place tst)
			 else findValue x (Rem tst) 
		end

fun findOper x empt = ""
	| findOper x tst =
			if (Name tst = x) then (Oper tst)
			else findOper x (Rem tst)
(*TEMP SYMBOL TABLE OVER*)


(*SYMBOL TABLE,TOKENS,CODE GENERATION,DATATYPES AND HELPER FUNCTIONS*)
datatype valu = none | integer of int | boolean of bool
datatype 'a SymbolT = empty | Entry of 'a * int * valu * 'a SymbolT


type da = string
type b = int
datatype 'a tokens =
	Empty | Token of 'a * b * b * 'a tokens

datatype 'c hybrid =
	Null | cons of 'c tokens list * 'c SymbolT * 'c TempST * 'c list

fun tokenp Null = []
	| tokenp (cons(a,_,_,_)) = a

fun symbt Null = empty
	| symbt (cons(_,b,_,_)) = b
 
fun codep Null = []
	| codep (cons(_,_,_,c)) = c

fun tempp Null = empt
	| tempp (cons(_,_,d,_)) = d
	

exception notoken
exception nost

fun value Empty = raise notoken
	| value (Token(a,_,_,_)) = a

fun valueLW Empty = raise notoken
	| valueLW (Token(_,a,b,_)) = (a::(b::[]))  

fun valueE Empty = Empty
	| valueE (Token(_,_,_,a)) = a

fun Error "semantic1" [l,w] =
	let val b = Int.toString l
			val c = Int.toString w
			val a = concat (["Semantic error at ",b,".",c])
			val e = Token(a,0,0,Empty)
	in cons([Token("1Fail",0,0,e)],empty,empt,[])
	end
	| Error "syntax" [l,w]  = 
	let val b = Int.toString l
			val c = Int.toString w
			val a = concat (["Syntax error at ",b,".",c])
			val e = Token(a,0,0,Empty)
	in cons([Token("1Fail",0,0,e)],empty,empt,[])
	end
	| Error _ _ = cons([Empty],empty,empt,[])

fun Error1 "lexing" [l,w] = [Token("1LFail",l,w,Empty)]
	| Error1 _ _ = [Empty]


(*SYMBOL TABLE START*)

fun EType (Entry(_,a,_,_)) = a
	| EType empty = raise nost
fun ETable (Entry(_,_,_,b)) = b
	| ETable empty = raise nost
fun EName (Entry(c,_,_,_)) = c 
	| EName empty = raise nost
fun EValue (Entry(_,_,v,_)) = v
	| EValue empty = raise nost

fun Lookup x empty = false
	| Lookup x (Entry(a,_,_,c)) = 
			if (x=a) then true 
			else Lookup x c

fun CheckType x y empty = true
	| CheckType x y (Entry(a,b,d,c)) =
		if (x=a) andalso (y=b) then true
		else if (x=a) then false
		else CheckType x y c

fun ReturnType x empty = ~1
	| ReturnType x (Entry(a,b,_,c)) =
			if (x = a) then b
			else ReturnType x c


fun AddEntry x y st = Entry(x,y,none,st)  
		
fun AddType x y empty = empty 
	| AddType x y st= 
		let
			val z = EName st 
		in 
			if (z=x) then Entry(x,y,(EValue st),(ETable st))
			else Entry(z,(EType st),(EValue st),(AddType x y (ETable st)))
		end

fun DeclaredOnlyOnce name st = not (Lookup name st) 
fun UseAfterDec name typ st = Lookup name st
fun UseCorrectType name typ st = CheckType name typ st 

fun updatelastn num st typ = 
	if num <= 0 then st
	else
		let val symt = Entry((EName st),typ,none,(updatelastn (num-1) (ETable st) typ)) 
		in symt
		end
 

(*SYMBOL TABLE OVER*)
(*SYMBOL TABLE,TOKENS,CODE GENERATION,DATATYPES AND HELPER FUNCTIONS*)



(*THE CHARACHTER AND SYMBOL SET OF THE LANGUAGE*)
val RelOp = ["<","<=","=",">",">=","<>"]
val AddOp = ["+","-"]
val MultOp = ["*","/","%"]
val Sign = ["~","+"]
val BinOp = ["||","&&"]
val UpperCase = ["A","B","C","D","E","F","G","H","I","J","K","L","M","N","O","P","Q","R","S","T","U","V","W","X","Y","Z"]
val LowerCase = ["a","b","c","d","e","f","g","h","i","j","k","l","m","n","o","p","q","r","s","t","u","v","w","x","y","z"]
val Digit = ["0","1","2","3","4","5","6","7","8","9"]
val SpecialChar = ["!","'","#","$","%","&","(",")","*","+",",","-",".","/",":",";","<","=",">","?","@","[","\\","]","|","^","|","{","}","_","~"]
val Keywords = ["program","var","int","bool","read","write","if","then","else","endif","while","do","endwh","tt","ff"]



(*SOME HELPING FUNCTIONS TO CHECK IF TOKENS ARE IDENTIFIERS OR NUMERALS*)
fun exists [] value = false
	| exists (h::t) value = 
		if (h=value) then true
		else true andalso exists t value

fun isLetter cha = exists (UpperCase@LowerCase) cha
fun isDigit cha = exists Digit cha

fun isLetterDigitList [] = true
	| isLetterDigitList (h::rest) = (exists (UpperCase@LowerCase@Digit) h) andalso (isLetterDigitList rest)

fun isIdent token = 
	let val tokene = explode token
			val tokenestr = map str tokene
	in (isLetter (hd tokenestr)) andalso (isLetterDigitList tokenestr)
	end

fun isDigitList [] = true 
	| isDigitList (h::t) = (isDigit h) andalso (isDigitList t)

fun isNumeral token =
	let val tokene = explode token
			val tokenestr = map str tokene
	in (isDigit (hd tokenestr)) andalso (isDigitList (tl tokenestr))
	end


fun Identifier (cons(tokens,st,tst,code)) = 
		if isIdent (value (hd tokens)) = true then (cons((tl tokens),st,tst,code))
		else
			let val rest1 = Error "syntax" (valueLW (hd tokens))
			in cons((tl tokens),st,tst,code)
			end
	| Identifier Null = Error "syntax" [0,0]

fun updateSymbolTable (cons(tokens,st,tst,code)) =
	if isIdent (value (hd tokens)) = true then 
		if (Lookup (value (hd tokens)) st = false) then 
				let val symt = AddEntry (value (hd tokens)) ~1 st
 				in updateSymbolTable (cons((tl tokens),symt,tst,code))
				end
			else Error "semantic1" (valueLW (hd tokens))
	else if (value (hd tokens) = ",") then updateSymbolTable (cons((tl tokens),st,tst,code))
	else if (value (hd tokens) = ":") then (cons((tl tokens),st,tst,code))
	else (cons(tokens,st,tst,code))
	| updateSymbolTable Null = Error "syntax" [0,0]
(*END OF HELPER FUNCTIONS *)



(*LEXING AND SCANNING STARTS*)
fun dfa state listofchars linenum wordnum tokenlist tokenforming= 
	if listofchars = [] andalso tokenforming = "" then tokenlist
	else if listofchars = [] then tokenlist @ ((Token(tokenforming,linenum,wordnum,Empty))::[])
	else
		if (exists (UpperCase@LowerCase) (hd listofchars)) andalso state = "start" then 
			dfa "identifier" (tl listofchars) linenum (wordnum) tokenlist (concat([tokenforming,(hd listofchars)]))
		else if (state = "start") andalso (exists Digit (hd listofchars)) then
			dfa "numeral" (tl listofchars) linenum (wordnum) tokenlist (concat([tokenforming,(hd listofchars)]))
		else if (state = "start") andalso (exists SpecialChar (hd listofchars)) then
			if (hd listofchars) = "|" andalso (hd (tl listofchars)) = "|" then 
				dfa "start" (tl (tl listofchars)) linenum (wordnum+1) (tokenlist@((Token("||",linenum,wordnum,Empty))::[]) ) ""
			else if ( (hd listofchars = "&") andalso ((hd (tl listofchars)) = "&") ) then 
				dfa "start" (tl (tl listofchars)) linenum (wordnum+1) (tokenlist@((Token("&&",linenum,wordnum,Empty))::[]) ) ""
			else if ((hd listofchars = "<") andalso ((hd (tl listofchars)) = "=")) then 
				dfa "start" (tl (tl listofchars)) linenum (wordnum+1) (tokenlist@((Token("<=",linenum,wordnum,Empty))::[]) ) ""
			else if ((hd listofchars = "<") andalso ((hd (tl listofchars)) = ">")) then 
				dfa "start" (tl (tl listofchars)) linenum (wordnum+1) (tokenlist@((Token("<>",linenum,wordnum,Empty))::[]) ) ""
			else if (hd listofchars = "<") then 
				dfa "start" (tl (listofchars)) linenum (wordnum+1) (tokenlist@((Token("<",linenum,wordnum,Empty))::[]) ) ""
			else if hd listofchars = ">" andalso (hd (tl listofchars)) = "=" then 
				dfa "start" (tl (tl listofchars)) linenum (wordnum+1) (tokenlist@((Token(">=",linenum,wordnum,Empty))::[]) ) ""
			else if hd listofchars = ">" then 
				dfa "start" (tl (listofchars)) linenum (wordnum+1) (tokenlist@((Token(">",linenum,wordnum,Empty))::[]) ) ""
			else if hd listofchars = "=" then 
				dfa "start" (tl (listofchars)) linenum (wordnum+1) (tokenlist@((Token("=",linenum,wordnum,Empty))::[]) ) ""
			else if hd listofchars = ":" andalso ((hd (tl listofchars)) = "=") then 
				dfa "start" (tl (tl listofchars)) linenum (wordnum+1) (tokenlist@((Token(":=",linenum,wordnum,Empty))::[]) ) ""
			else if hd listofchars = ":" andalso ((hd (tl listofchars)) = ":") then 
				dfa "start" (tl (tl listofchars)) linenum (wordnum+1) (tokenlist@((Token("::",linenum,wordnum,Empty))::[]) ) ""
			else 
				dfa "start" (tl (listofchars)) linenum (wordnum+1) (tokenlist@((Token(hd listofchars,linenum,wordnum,Empty))::[]) ) ""
		else if (state = "start") andalso (hd listofchars = " ") then
			dfa "start" ((tl listofchars)) linenum wordnum tokenlist ""
		else if (exists (UpperCase@LowerCase@Digit) (hd listofchars)) andalso state = "identifier" then 
			dfa "identifier" (tl listofchars) linenum wordnum tokenlist (concat([tokenforming,(hd listofchars)]))
		else if (state = "identifier") then 
			dfa "start" ((listofchars)) linenum (wordnum+1) (tokenlist @ ((Token(tokenforming,linenum,wordnum,Empty))::[]) ) ""
		else if state = "numeral" andalso (exists Digit (hd listofchars)) then
			dfa "numeral" (tl listofchars) linenum (wordnum) tokenlist (concat([tokenforming,(hd listofchars)]))
		else if (state = "numeral") then
			dfa "start" ((listofchars)) linenum (wordnum+1) (tokenlist@((Token(tokenforming,linenum,wordnum,Empty))::[]) ) ""
		else Error1 "lexing" [linenum,wordnum]



fun Tokenise multiline n listoftokens = 
	if (multiline = []) then listoftokens
	else 
		let val line = hd multiline
				val listofchars = map str (explode line)
				val tokens = dfa "start" listofchars n 1 [] ""
				val newtokens = listoftokens @ tokens
		in Tokenise (tl multiline) (n+1) newtokens 
		end
(*LEXING AND SCANNING OVER*)



(*PARSING STARTS*)
fun Variable Null = raise notoken
	| Variable (cons([],st,tst,code)) = Error "syntax" [0,0]
	| Variable (cons(tokens,st,tst,code)) =
		if isIdent (value (hd tokens)) = true then 
			let val rest1 = PlusComb "Variable" tst
					val newtst = PlusPlace "Variable" (stri( value (hd tokens) )) rest1
			in (cons((tl tokens),st,newtst,code))
			end
		else Error "syntax" (valueLW (hd tokens))

fun Variable_more (cons([],st,tst,code)) = Error "syntax" [0,0]
	| Variable_more (cons(tokens,st,tst,code)) = 
	if (value (hd tokens) = ",") then VariableList (cons((tl tokens),st,tst,code))
	else if (value (hd tokens) = ":") then (cons((tl tokens),st,tst,code))
	else Error "syntax" (valueLW (hd tokens))
	| Variable_more Null = Error "syntax" [0,0]


and VariableList (cons(tokens,st,tst,code)) =
	let val rest = Variable (cons(tokens,st,tst,code))
			val rest1 = Variable_more rest
	in 
		if rest1 = cons([Token("1Fail",0,0,Empty)],empty,empt,[]) then rest1 
		else 
			let val sym = updateSymbolTable (cons(tokens,st,tst,code))
			in cons((tokenp rest1),(symbt sym),tst,code)
			end
	end
	| VariableList Null = Error "syntax" [0,0]

fun Type num_vars (cons([],st,tst,code)) = Error "syntax" [0,0]
	| Type num_vars (cons(tokens,st,tst,code)) =  
	if (value (hd tokens) = "int") then
		let val syt = updatelastn num_vars st 0
		in cons((tl tokens),syt,tst,code)
		end
	else if (value (hd tokens) = "bool") then 
		let val syt = updatelastn num_vars st 1
		in cons((tl tokens),syt,tst,code)
		end
	else Error "syntax" (valueLW (hd tokens))
	| Type _ Null = Error "syntax" [0,0]

fun numvariables num tokens = 
	if (value (hd tokens)) = ":" then num
	else if (isIdent (value (hd tokens))) then 
		if (value (hd (tl tokens))) = ":" then num+1
		else numvariables (num+1) (tl tokens)
	else if (value (hd tokens)) = "," then numvariables num (tl tokens)
	else ~1
	
fun Declaration (cons(tokens,st,tst,code)) = 
	let val rest = VariableList (cons(tokens,st,tst,code))
			val num_vars = numvariables 0 tokens
			val rest1 = Type num_vars rest
	in if (value (hd (tokenp rest1))) = ";" then cons((tl (tokenp rest1)),symbt rest1,tst,code)
		 else Error "syntax" (valueLW (hd tokens))  
	end
	| Declaration Null = Error "syntax" [0,0] 	
	

fun DeclarationSeq (cons([],st,tst,code)) = (cons([],st,tst,code))
	| DeclarationSeq (cons(tokens,st,tst,code)) = 
	if (value (hd tokens)) = "var" then
		let val rest = Declaration (cons((tl tokens),st,tst,code))
		in DeclarationSeq rest
		end
	else cons(tokens,st,tst,code)
	| DeclarationSeq Null = Error "syntax" [0,0]

(* INTEGER EXPRESSIONS *)
fun IntT1 (cons([],st,tst,code)) = cons([],st,tst,code)
	| IntT1 (cons(tokens,st,tst,code)) = 
		if (exists MultOp (value (hd tokens))) then 
			let val rest1 = IntFactor (cons((tl tokens),st,tst,[]))
					val IFCode = codep rest1
					val IFPlace = findPlace "IntFactor" (tempp rest1)
					val rest2 = IntT1 (cons(tokenp rest1,symbt rest1,tempp rest1,[]))
					val IT11Code = codep rest2
					val IT11Place = findPlace "IntT1" (tempp rest2)
					val IT11Oper = findOper "IntT1" (tempp rest2)
					val rhs = concat ( [IFPlace] @ [" "] @ [IT11Oper] @ [" "] @ [IT11Place] )
					val newtst = PlusComb "IntT1" (tempp rest2)
					val newwtst = PlusPlace "IntT1" (stri("IT1")) newtst
					val newwwtst = PlusOper "IntT1" (value (hd tokens)) newwtst
					val assign = concat (["IT1 := "]@ [rhs])
					val codefinal = code @ IFCode @ IT11Code @ [assign] 
			in cons((tokenp rest2),(symbt rest2),newwwtst,codefinal)
			end
		else 
				let val newtst = PlusComb "IntT1" tst
						val newwtst = PlusPlace "IntT1" (stri("1")) newtst
						val newwwtst = PlusOper "IntT1" " * " newwtst
				in (cons(tokens,st,newwwtst,code))
				end
	| IntT1 Null = Error "syntax" [0,0]


and IntFactor (cons([],st,tst,code)) = (cons([],st,tst,code))
	| IntFactor (cons(tokens,st,tst,code)) = 
		if (isNumeral (value (hd tokens))) then 
			let val newtst = PlusComb "IntFactor" tst
					val newwtst = PlusPlace "IntFactor" (stri("IF")) newtst
					val assign = concat ( ["IF := "] @ [ (value (hd tokens)) ]  )
					val codefinal = code @ [assign]
			in cons((tl tokens),st,newwtst,codefinal)
			end
		else if ( value (hd tokens) = "(" ) then 
			let val rest1 = IntExpression (cons((tl tokens),st,tst,[]))
					val IECode = codep rest1
					val IEPlace = findPlace "IntExpression" (tempp rest1)
					val newtst = PlusComb "IntFactor" (tempp rest1)
					val newwtst = PlusPlace "IntFactor" (stri("IF")) newtst
					val assign = concat ( ["IF := "] @ [IEPlace] )
					val codefinal = code @ IECode @ [assign]
			in if (value (hd (tokenp rest1)) = ")") then cons((tl (tokenp rest1)),symbt rest1,newwtst,codefinal)
				 else Error "syntax" (valueLW (hd (tokenp rest1)))
			end
		else if (value (hd tokens) = "~") then 
			let val rest1 = IntFactor (cons((tl tokens),st,tst,[]) ) 
					val IF0Code = codep rest1
					val IF0Place = findPlace "IntFactor" (tempp rest1)
					val newtst = PlusComb "IntFactor" (tempp rest1)
					val newwtst = PlusPlace "IntFactor" (stri("IF")) newtst
					val assign = concat ( ["IF :=  0 - "] @ [IF0Place] )
					val codefinal = code @ IF0Code @ [assign]
			in cons(((tokenp rest1)),symbt rest1,newwtst,codefinal)
			end
		else if (isIdent (value (hd tokens))) then 
			let val a = CheckType (value (hd tokens)) 0 st
					val b = Lookup (value (hd tokens)) st
			in
				if (a = true andalso b = true) then 
					let val rest1 = Variable (cons(tokens,st,tst,[]))
							val VarPlace = findPlace "Variable" (tempp rest1)
							val newtst = PlusComb "IntFactor" (tempp rest1)
							val newwtst = PlusPlace "IntFactor" (stri("IF")) newtst
							val assign = concat ( ["IF := "] @ [(value (hd tokens))] )
							val codefinal = code @ [assign]
					in cons(((tokenp rest1)),symbt rest1,newwtst,codefinal)
					end
				else Error "semantic1" (valueLW (hd tokens))
			end
		else Error "syntax" (valueLW (hd tokens))
	| IntFactor Null = Error "syntax" [0,0]

and IntTerm (cons([],st,tst,code)) = (cons([],st,tst,code))
	| IntTerm (cons(tokens,st,tst,code)) = 
			let val rest1 = IntFactor (cons(tokens,st,tst,[]))
					val IFCode = codep rest1
					val IFPlace = findPlace "IntFactor" (tempp rest1)
					val rest2 = IntT1 (cons(tokenp rest1,symbt rest1,tempp rest1,[]))
					val IT1Place = findPlace "IntT1" (tempp rest2)
					val IT1Oper = findOper "IntT1" (tempp rest2)
					val IT1Code = codep rest2
					val rhs = concat ( [IFPlace] @ [" "] @[IT1Oper] @ [" "] @ [IT1Place] )
					val newtst = PlusComb "IntTerm" (tempp rest2)
					val newwtst = PlusPlace "IntTerm" (stri("IT")) newtst
					val assign = concat ( ["IT := "] @ [rhs] )
					val codefinal = code @ IFCode @ IT1Code @ [assign]
			in cons((tokenp rest2),(symbt rest2),newwtst,codefinal)
			end
	| IntTerm Null = Error "syntax" [0,0]

and IntExp1 (cons([],st,tst,code)) = (cons([],st,tst,code))
	|	IntExp1 (cons(tokens,st,tst,code)) = 
			if (exists AddOp (value (hd tokens))) then 
				let val rest1 = IntTerm (cons((tl tokens),st,tst,[]))
						val ITCode = codep rest1
						val ITPlace = findPlace "IntTerm" (tempp rest1)
						val rest2 = IntExp1 (cons(tokenp rest1,symbt rest1,tempp rest1,[]))
						val IE11Code = codep rest2
						val IE11Place = findPlace "IntExp1" (tempp rest2)
						val IE11Oper = findOper "IntExp1" (tempp rest2)
						val rhs = concat ( [ITPlace] @ [" "] @ [IE11Oper] @ [" "] @ [IE11Place] )
						val newtst = PlusComb "IntExp1" (tempp rest2)
						val newwtst = PlusPlace "IntExp1" (stri("IE1")) newtst
						val newwwtst = PlusOper "IntExp1" (value (hd tokens)) newwtst
						val assign = concat (["IE1 := "]@ [rhs])
						val codefinal = code @ ITCode @ IE11Code @ [assign]
				in cons((tokenp rest2),(symbt rest2),newwwtst,codefinal)
				end  
			else 
				let val newtst = PlusComb "IntExp1" tst
						val newwtst = PlusPlace "IntExp1" (stri("0")) newtst
						val newwwtst = PlusOper "IntExp1" " + " newwtst
				in (cons(tokens,st,newwwtst,code))
				end
	| IntExp1 Null = Error "syntax" [0,0]

and IntExpression (cons([],st,tst,code)) = (cons([],st,tst,code))
	| IntExpression (cons(tokens,st,tst,code)) = 
			let val rest1 = IntTerm (cons(tokens,st,tst,[]))
					val ITCode = codep rest1 
					val ITPlace = findPlace "IntTerm" (tempp rest1)
					val rest2 = IntExp1 (cons(tokenp rest1,symbt rest1,tempp rest1,[]))
					val IE1Place = findPlace "IntExp1" (tempp rest2)
					val IE1Oper = findOper "IntExp1" (tempp rest2)
					val IE1Code = codep rest2
					val rhs = concat ([ITPlace] @ [" "] @ [IE1Oper] @ [" "] @ [IE1Place])
					val newtst = PlusComb "IntExpression" (tempp rest2)
					val newwtst = PlusPlace "IntExpression" (stri("IE")) newtst
					val assign = concat ( ["IE := "]  @ [rhs] )
					val codefinal = code @ ITCode @ IE1Code @ [assign]
			in cons((tokenp rest2),(symbt rest2),newwtst,codefinal)
			end
	| IntExpression Null = Error "syntax" [0,0]
	
(*INT EXPRESSIONS OVER*)

fun Comparison (cons([],st,tst,code)) = Error "syntax" [0,0]
	| Comparison (cons(token,st,tst,code)) =
	let val rest1 = IntExpression (cons(token,st,tst,[]))
			val IE1Code = codep rest1
			val IE1Place = findPlace "IntExpression" (tempp rest1)
	in if (exists RelOp (value (hd (tokenp rest1)))) then 
				let val rest2 = IntExpression (cons((tl (tokenp rest1)),symbt rest1,(tempp rest1),[]))
						val IE2Code = codep rest2
						val IE2Place = findPlace "IntExpression" (tempp rest2)
						val newtst = PlusComb "Comparison" (tempp rest2)
						val newwtst = PlusPlace "Comparison" (stri("Comp")) newtst
						val rhs = concat ( [IE1Place] @ [" "] @ [(value (hd (tokenp rest1)))] @ [" "] @ [IE2Place] )
						val expr = concat ( ["Comp := "] @ [rhs]  )
						val codefinal = code @ IE1Code @ IE2Code @ [expr]
				in cons(tokenp rest2,symbt rest2,newwtst,codefinal)
				end
		 else Error "syntax" (valueLW (hd (tokenp rest1) ))
	end
	| Comparison Null = Error "syntax" [0,0]

(*BOOL EXPRESSIONS*)
fun BoolT1 (cons([],st,tst,code)) = (cons([],st,tst,code))
	| BoolT1 (cons(tokens,st,tst,code)) = 
		if (value (hd tokens) = "&&") then 
			let val rest1 = BoolFactor (cons((tl tokens),st,tst,[]))
					val BFCode = codep rest1
					val BFPlace = findPlace "BoolFactor" (tempp rest1)
					val rest2 = BoolT1 (cons(tokenp rest1,symbt rest1,tempp rest1,[]))
					val BT11Code = codep rest2
					val BT11Place = findPlace "BoolT1" (tempp rest2)
					val BT11Oper = findOper "BoolT1" (tempp rest2)
					val rhs = concat ( [BFPlace] @ [" "] @ [BT11Oper] @ [" "] @ [BT11Place] )
					val newtst = PlusComb "BoolT1" (tempp rest2)
					val newwtst = PlusPlace "BoolT1" (stri("BT1")) newtst
					val newwwtst = PlusOper "BoolT1" (value (hd tokens)) newwtst
					val assign = concat (["BT1 := "]@ [rhs])
					val codefinal = code @ BFCode @ BT11Code @ [assign] 
			in cons((tokenp rest2),(symbt rest2),newwwtst,codefinal)
			end
		else 
				let val newtst = PlusComb "BoolT1" tst
						val newwtst = PlusPlace "BoolT1" (stri("true")) newtst
						val newwwtst = PlusOper "BoolT1" " && " newwtst
				in (cons(tokens,st,newwwtst,code))
				end
	| BoolT1 Null = Error "syntax" [0,0]

and BoolFactor (cons([],st,tst,code)) = (cons([],st,tst,code))
	| BoolFactor (cons(tokens,st,tst,code)) = 
		if (value (hd tokens) = "tt") then 
			let val newtst = PlusComb "BoolFactor" tst
					val newwtst = PlusPlace "BoolFactor" (stri ("BF")) newtst
					val assign = concat ( ["BF := " ] @ ["true"] )
					val codefinal = code @ [assign] 
			in (cons(tl tokens,st,newwtst,codefinal)) 
			end
		else if (value (hd tokens) = "ff") then 
			let val newtst = PlusComb "BoolFactor" tst
					val newwtst = PlusPlace "BoolFactor" (stri ("BF")) newtst
					val assign = concat ( ["BF := " ] @ ["false"] )
					val codefinal = code @ [assign] 
			in (cons(tl tokens,st,newwtst,codefinal)) 
			end
		else if (value (hd tokens) = "(" ) then 
			let val rest1 = BoolExpression (cons((tl tokens),st,tst,[]))
					val BECode = codep rest1
					val BEPlace = findPlace "BoolExpression" (tempp rest1)
					val newtst = PlusComb "BoolFactor" (tempp rest1)
					val newwtst = PlusPlace "BoolFactor" (stri("BF")) newtst
					val assign = concat ( ["BF := "] @ [BEPlace] )
					val codefinal = code @ BECode @ [assign]
			in if (value (hd (tokenp rest1)) = ")") then cons((tl (tokenp rest1)),symbt rest1,newwtst,codefinal)
				 else Error "syntax" (valueLW (hd (tokenp rest1)))
			end
		else if (value (hd tokens) = "!") then 
			let val rest1 = BoolFactor (cons((tl tokens),st,tst,[]) ) 
					val BF0Code = codep rest1
					val BF0Place = findPlace "BoolFactor" (tempp rest1)
					val newtst = PlusComb "BoolFactor" (tempp rest1)
					val newwtst = PlusPlace "BoolFactor" (stri("BF")) newtst
					val assign = concat ( ["BF := not "] @ [BF0Place] )
					val codefinal = code @ BF0Code @ [assign]
			in cons(((tokenp rest1)),symbt rest1,newwtst,codefinal)
			end
		else if (isIdent (value (hd tokens))) andalso (exists RelOp (value (hd (tl tokens)) ))= false then 
			let val a = CheckType (value (hd tokens)) 1 st  (*TYPE CHECKING*)
					val b = Lookup (value (hd tokens)) st        (*DECLARED BEFORE USE*)
			in
				if (a = true andalso b = true) then 
					let val rest1 = Variable (cons(tokens,st,tst,[]))
							val VarPlace = findPlace "Variable" (tempp rest1)
							val newtst = PlusComb "BoolFactor" (tempp rest1)
							val newwtst = PlusPlace "BoolFactor" (stri("BF")) newtst
							val assign = concat ( ["BF := "] @ [VarPlace] )
							val codefinal = code @ [assign]
					in cons(((tokenp rest1)),symbt rest1,newwtst,codefinal)
					end
				else Error "semantic1" (valueLW (hd tokens))
			end
		else
			let val rest1 = Comparison (cons(tokens,st,tst,[]))
					val ComPlace = findPlace "Comparison" (tempp rest1)
					val ComCode = codep rest1
					val newtst = PlusComb "BoolFactor" (tempp rest1)
					val newwtst = PlusPlace "BoolFactor" (stri("BF")) newtst
					val assign = concat ( ["BF := "] @ [ComPlace] )
					val codefinal = code @ ComCode @ [assign]
			in cons(((tokenp rest1)),symbt rest1,newwtst,codefinal)
			end
	| BoolFactor Null = Error "syntax" [0,0]

and BoolTerm (cons([],st,tst,code)) = (cons([],st,tst,code))
	| BoolTerm (cons(tokens,st,tst,code)) = 
			let val rest1 = BoolFactor (cons(tokens,st,tst,[]))
					val BFCode = codep rest1
					val BFPlace = findPlace "BoolFactor" (tempp rest1)
					val rest2 = BoolT1 (cons(tokenp rest1,symbt rest1,tempp rest1,[]))
					val BT1Place = findPlace "BoolT1" (tempp rest2)
					val BT1Oper = findOper "BoolT1" (tempp rest2)
					val BT1Code = codep rest2
					val rhs = concat ( [BFPlace] @ [" "] @ [BT1Oper] @ [" "] @ [BT1Place] )
					val newtst = PlusComb "BoolTerm" (tempp rest2)
					val newwtst = PlusPlace "BoolTerm" (stri("BT")) newtst
					val assign = concat ( ["BT := "] @ [rhs] )
					val codefinal = code @ BFCode @ BT1Code @ [assign]
			in cons((tokenp rest2),(symbt rest2),newwtst,codefinal)
			end
	| BoolTerm Null = Error "syntax" [0,0]

and BoolExp1 (cons([],st,tst,code)) = (cons([],st,tst,code))
	| BoolExp1 Null = Error "syntax" [0,0]
	| BoolExp1 (cons(tokens,st,tst,code)) = 
		if (value (hd tokens) = "||") then
			let val rest1 = BoolTerm (cons((tl tokens),st,tst,[]))
					val BTCode = codep rest1
					val BTPlace = findPlace "BoolTerm" (tempp rest1)
					val rest2 = BoolExp1 (cons(tokenp rest1,symbt rest1,tempp rest1,[]))
					val BE11Code = codep rest2
					val BE11Place = findPlace "BoolExp1" (tempp rest2)
					val BE11Oper = findOper "BoolExp1" (tempp rest2)
					val rhs = concat ( [BTPlace] @ [" "] @ [BE11Oper] @ [" "] @ [BE11Place] )
					val newtst = PlusComb "BoolExp1" (tempp rest2)
					val newwtst = PlusPlace "BoolExp1" (stri("BE1")) newtst
					val newwwtst = PlusOper "BoolExp1" (value (hd tokens)) newwtst
					val assign = concat (["BE1 := "]@ [rhs])
					val codefinal = code @ BTCode @ BE11Code @ [assign]
				in cons((tokenp rest2),(symbt rest2),newwwtst,codefinal)
				end   
		else 
			let val newtst = PlusComb "BoolExp1" tst
					val newwtst = PlusPlace "BoolExp1" (stri("false")) newtst
					val newwwtst = PlusOper "BoolExp1" " || " newwtst
				in (cons(tokens,st,newwwtst,code))
				end
	

and BoolExpression (cons([],st,tst,code)) = (cons([],st,tst,code))
	| BoolExpression Null = Error "syntax" [0,0]
	| BoolExpression (cons(tokens,st,tst,code)) = 
			let val rest1 = BoolTerm (cons(tokens,st,tst,[]))
					val BTCode = codep rest1 
					val BTPlace = findPlace "BoolTerm" (tempp rest1)
					val rest2 = BoolExp1 (cons(tokenp rest1,symbt rest1,tempp rest1,[]))
					val BE1Place = findPlace "BoolExp1" (tempp rest2)
					val BE1Oper = findOper "BoolExp1" (tempp rest2)
					val BE1Code = codep rest2
					val rhs = concat ([BTPlace] @ [" "] @ [BE1Oper] @ [" "] @ [BE1Place])
					val newtst = PlusComb "BoolExpression" (tempp rest2)
					val newwtst = PlusPlace "BoolExpression" (stri("BE")) newtst
					val assign = concat ( ["BE := "]  @ [rhs] )
					val codefinal = code @ BTCode @ BE1Code @ [assign]
			in cons((tokenp rest2),(symbt rest2),newwtst,codefinal)
			end

(*BOOL EXPRESSIONS OVER*)

fun Expression tokens = 
	let 
		val rest1 = IntExpression tokens
		val rest3 = PlusComb "Expression" (tempp rest1)
		val newtst = PlusPlace "Expression" (findValue "IntExpression" rest3) rest3
	in 
		if value (hd (tokenp rest1)) = "0fail" then
			let val rest2 = BoolExpression tokens
					val rest4 = PlusComb "Expression" (tempp rest2)
					val newwtst = PlusPlace "Expression" (findValue "BoolExpression" rest4) rest4
			in (cons(tokenp rest2,symbt rest2,newwtst,codep rest2))
			end
		else (cons(tokenp rest1,symbt rest1,newtst,codep rest1))
	end 

fun inss tillnow file x = 
	if (x < tillnow) then inss tillnow (tl file) (x+1)
		else if (x = tillnow) then tl (file) 
		else file
	

fun Command (cons([],st,tst,code)) = Error "syntax" [0,0]
	| Command Null = Error "syntax" [0,0] 
	| Command (cons(tokens,st,tst,code)) = 
	let val tillnow = length code
	in 
		if (value (hd tokens) = "read") then
			let val rest1 = Variable (cons((tl tokens),st,tst,[]))
					val VPlace = (findPlace "Variable" (tempp rest1))
					val ir_var = codep rest1
					val read = ["read value"]
					val assign = concat ([VPlace]@[ " := value"])
					val codefinal = code @ read @ [assign]					
			in (cons((tokenp rest1),(symbt rest1),(tempp rest1),codefinal))
			end
		else if (value (hd tokens) = "write") then 
			let val rest1 = IntExpression (cons((tl tokens),st,tst,[]))
					val IEPlace = (findPlace "IntExpression" (tempp rest1))
					val ir_inte = codep rest1
					val write =  concat (["write := "] @ [IEPlace])
					val codefinal = code @ ir_inte @ [write]
			in (cons((tokenp rest1),(symbt rest1),(tempp rest1),codefinal))
			end
		else if (value (hd tokens) = "if") then
			let val rest1 = BoolExpression (cons((tl tokens),st,tst,code))
					val totalcode = codep rest1
					val ir_cond = inss tillnow totalcode 1
					val ir_condl = length ir_cond
					val BEplace = (findPlace "BoolExpression" (tempp rest1)) 
			in if (value (hd (tokenp rest1)) = "then") then
				let val tillnow1 = (length totalcode) + 1
						val rest2 = CommandSeq (cons((tl (tokenp rest1)),symbt rest1,(tempp rest1),totalcode @ [""]))
						val totalcode2 = codep rest2
						val ir_cs1 = inss tillnow1 totalcode2 1
						val ir_cs1l = length ir_cs1
				in if (value (hd (tokenp rest2)) = "else") then
					let val tillnow2 = 1 + (length totalcode2)
							val rest3 = CommandSeq (cons((tl (tokenp rest2)),symbt rest2,(tempp rest2),totalcode2 @ [""]))
							val totalcode3 = codep rest3
							val ir_cs2 = inss tillnow2 totalcode3 1
							val ir_cs2l = length ir_cs2
					in 
						if (value (hd (tokenp rest3)) = "endif") then
							let val pos2 = tillnow2+1
									val pos3 = (length totalcode3)+1
									val conditional = concat (["if "]@[(BEplace)]@[" = 1 goto "]@[(Int.toString pos2)] )
									val jump = concat (["goto "]@[(Int.toString pos3)])
									val codefinal = code @ ir_cond @ [conditional] @ ir_cs1 @ [jump] @ ir_cs2		
							in (cons((tl (tokenp rest3)),symbt rest3,tst,codefinal))
							end
					 else Error "syntax" (valueLW (hd (tokenp rest3)))
					end
						else Error "syntax" (valueLW (hd (tokenp rest2)))
				end
			 else Error "syntax" (valueLW (hd (tokenp rest1)))
		end
	else if (value (hd tokens) = "while") then 	
		let val rest1 = BoolExpression (cons((tl tokens),st,tst,code))
				val totalcode = codep rest1
				val ir_cond = inss tillnow totalcode 1 
				val ir_condl = length ir_cond
				val BEplace = (findPlace "BoolExpression" (tempp rest1)) 
		in if (value (hd (tokenp rest1)) = "do") then
				let val tillnow1 = (length totalcode) + 1
						val rest2 = CommandSeq (cons((tl (tokenp rest1)),symbt rest1,(tempp rest1),totalcode @ [""]))
						val totalcode2 = codep rest2
						val ir_cs1 = inss tillnow1 totalcode2 1
						val ir_cs1l = length ir_cs1
				in if (value (hd (tokenp rest2)) = "endwh") then 
							let val pos2 = tillnow + 1
									val pos3 = (length totalcode2)+2
									val conditional = concat (["if "]@[(BEplace)]@[" = 1 goto "]@[(Int.toString pos3)] )
									val jump = concat (["goto "]@[(Int.toString pos2)])
									val codefinal = code @ ir_cond @ [conditional] @ ir_cs1 @ [jump]
							in (cons((tl (tokenp rest2)),symbt rest2,(tempp rest2),codefinal))
							end
					 else Error "syntax" (valueLW (hd (tokenp rest2)))
				end
			 else Error "syntax" (valueLW (hd (tokenp rest1)))
		end
	else 
		let val rest1 = Variable (cons(tokens,st,tst,[]))
				val VPlace = (findPlace "Variable" (tempp rest1))
				val ir_var = codep rest1
				val typeofvar = ReturnType (value (hd tokens)) (symbt rest1)
		in if (value (hd (tokenp rest1)) = ":=") then 
				if (typeofvar = 0) then   (*integer*)
				let val rest2 = IntExpression (cons((tl (tokenp rest1)),symbt rest1,(tempp rest1),[]))
						val EPlace = (findPlace "IntExpression" (tempp rest2))
						val ir_exp = codep rest2
						val assign = concat ([VPlace] @ [" := "] @ [EPlace])
						val codefinal = code  @ ir_var @ ir_exp @ [assign]
				in (cons(((tokenp rest2)),symbt rest2,(tempp rest2),codefinal))
				end 
				else if (typeofvar = 1) then   (*boolean*)
				let val rest2 = BoolExpression (cons((tl (tokenp rest1)),symbt rest1,(tempp rest1),[]))
						val EPlace = (findPlace "BoolExpression" (tempp rest2))
						val ir_exp = codep rest2
						val assign = concat ([VPlace] @ [" := "] @ [EPlace])
						val codefinal = code  @ ir_var @ ir_exp @ [assign]
				in (cons(((tokenp rest2)),symbt rest2,(tempp rest2),codefinal))
				end 
				else Error "semantic1" (valueLW (hd (tokenp rest1)))
			 else Error "syntax" (valueLW (hd (tokenp rest1)))
		end
	end			

and Commands (cons([],st,tst,code)) = Error "syntax" [0,0]
	| Commands Null = Error "syntax" [0,0]
	| Commands (cons(tokens,st,tst,code)) = 
	if (value (hd tokens) = "}") then cons((tl tokens),st,tst,code)
	else 
		let val rest1 = Command (cons(tokens,st,tst,code))
		in 
			if (value (hd (tokenp rest1)) = ";") then Commands (cons((tl (tokenp rest1)),(symbt rest1),(tempp rest1),(codep rest1)))
			else Error "syntax" (valueLW (hd (tokenp rest1)))
		end		

and CommandSeq (cons([],st,tst,code)) = Error "syntax" [0,0]
	| CommandSeq Null = Error "syntax" [0,0]
	| CommandSeq (cons(tokens,st,tst,code)) = 
	if (value (hd tokens) = "{") then Commands (cons((tl tokens),st,tst,code))
	else Error "syntax" (valueLW (hd tokens))

fun Block tokens = 
	let val rest1 = DeclarationSeq tokens
			val rest2 = CommandSeq rest1
	in rest2
	end	 

fun Program (cons([Empty],st,tst,code)) = Error "syntax" [0,0]
	| Program Null = Error "syntax" [0,0]
	| Program (cons([],st,tst,code)) = Error "syntax" [0,0]
	| Program (cons(tokens,st,tst,code)) =
			let val head_value = (value (hd tokens))
					val newtst = PlusComb "Program" tst
			in
				if head_value = "program" then 
					let val rest = Identifier (cons((tl tokens),st,newtst,code))
						  val rest_head = value (hd (tokenp rest))
					in 
						if rest_head = "::" then 
							let val rest1 = Block (cons((tl (tokenp rest)),symbt rest,tst,code))
							in 
								if (tokenp rest1) = [] then cons([Token("1success",0,0,Empty)],symbt rest1,tempp rest1,(codep rest1))
								else Error "syntax" (valueLW (hd (tokenp rest1))) 
							end
						else Error "syntax" (valueLW ((hd (tokenp rest))))
					end
				else Error "syntax" (valueLW (hd tokens))
			end 
(*PARSING OVER*)



(*FILE HANDLING STARTS*)
open TextIO

fun bite (filename:string) =
    let val f = TextIO.getInstream(TextIO.openIn filename)
	fun loop (accum: string list, f) =
	    case TextIO.StreamIO.input f
	     of ("", f')    => (TextIO.StreamIO.closeIn f'; accum)
	      | (chunk, f') => loop (chunk::accum, f')	
    in  rev(loop ([], f))
    end

fun generateLines [] listofstrings stringf = listofstrings @ (stringf::[])
	| generateLines listofchars listofstrings stringf =
			if (hd listofchars = "\n") then generateLines (tl listofchars) (listofstrings @ (stringf::[])) ""
			else generateLines (tl listofchars) listofstrings (concat [stringf,hd listofchars])

fun writeLines(outFile: string, list: string list) =
  let
    val outStream = TextIO.openOut outFile
    fun out(xs : string list) =  
          case xs of
              [] => (TextIO.closeOut outStream)
            | x::xs' => (TextIO.output(outStream, x ^ "\r\n"); out(xs'))
  in
    out(list)
  end;

(*FILE HANDLING OVER*)

(*PUTTING IT ALL TOGETHER, CODE GENERATION / ERRORS FOUND*)
fun lexerrors [] errorl = errorl
	| lexerrors tokenl errorl = 
			if (value (hd tokenl) = "1LFail") then 
				let val [a,b] = valueLW (hd tokenl)
						val lc = Int.toString a
						val wc = Int.toString b
						val errorm = concat(["Scanning error at ",lc,".",wc])
						val errornew = errorl @ (errorm::[])
				in lexerrors (tl tokenl) errornew 
				end
		else lexerrors (tl tokenl) errorl

fun geterrorlist Empty errorlist = errorlist
	| geterrorlist result errorlist = 
	let val b = valueE result
			val c = value result
			val d = geterrorlist b (errorlist @ (c::[]))
	in d
	end
	

fun Execute tokenl = 
	let val result = Program (cons(tokenl,empty,empt,[]))
			val lexe = lexerrors tokenl []
	in if (value (hd (tokenp result))) = "1Fail" then cons([],empty,empt,["Errors found :"] @ lexe @ (geterrorlist (valueE (hd (tokenp result))) []))
		 else cons([],symbt result,empt,(codep result))
	end

(*gives the symbol table after parsing as result*)
fun execST sourcename =
	let val file = bite sourcename
			val a = concat file
			val b = explode a
			val c = map str b
			val finallines = generateLines c [] "" 
			val TOKENLIST = Tokenise finallines 1 []
			val cons(_,st,_,fresult) = Execute TOKENLIST
	in st
	end


(*COMPLETE*)

in

(*gives output as a string list with each line as one element*)
fun executefile sourcename =
	let val file = bite sourcename
			val a = concat file
			val b = explode a
			val c = map str b
			val finallines = generateLines c [] "" 
			val TOKENLIST = Tokenise finallines 1 []
			val cons(_,st,_,fresult) = Execute TOKENLIST
	in fresult
	end


(*writes result in file*)
fun writeResult inputfile outputfile = writeLines (outputfile, (executefile inputfile))

(*INTERPRETER STARTS*)

fun Interpreter sourcename = 

let 

(*datatype valu = none | integer of int | boolean of bool
datatype 'a SymbolT = empty | Entry of 'a * int * valu * 'a SymbolT*)
exception nost
exception noins
fun EType (Entry(_,a,_,_)) = a
	| EType empty = raise nost
fun ETable (Entry(_,_,_,b)) = b
	| ETable empty = raise nost
fun EName (Entry(c,_,_,_)) = c 
	| EName empty = raise nost
fun EValue (Entry(_,_,v,_)) = v
	| EValue empty = raise nost
fun EValueA (Entry(_,_,integer(b),_)) = Int.toString(b)
	| EValueA (Entry(_,_,boolean(b),_)) = Bool.toString(b)
	| EValueA (Entry(_,_,none,_)) = ""
	| EValueA empty = ""

fun RetAct x empty = none
	| RetAct x (Entry(a,_,b,c)) = 
		if x = a then b
		else RetAct x c

fun Lookup x empty = false
	| Lookup x (Entry(a,_,_,c)) = 
			if (x=a) then true 
			else Lookup x c

fun AddEntry x y z st = Entry(x,y,z,st)  
		
fun AddType x y empty = empty 
	| AddType x y st= 
		let
			val z = EName st 
		in 
			if (z=x) then Entry(x,y,(EValue st),(ETable st))
			else Entry(z,(EType st),(EValue st),(AddType x y (ETable st)))
		end

fun AddValue x y empty = empty
	| AddValue x y st = 
		let val z = EName st
		in if (z = x) then Entry(x,(EType st),y,(ETable st))
			 else Entry(z,EType st,EValue st,(AddValue x y (ETable st)))
		end

fun ReturnType x empty = ~1
	| ReturnType x (Entry(a,b,_,c)) =
			if (x = a) then b
			else ReturnType x c

datatype 'a fuse = Nothing | comb of 'a * string SymbolT * string SymbolT

fun combine d empty = d 
	| combine d (Entry(a1,b1,c1,d1)) = Entry(a1,b1,c1,(combine d d1))

fun DeleteEntry value empty bu = bu
	| DeleteEntry value (Entry(a,b,c,d)) bu =
		if (value = a) then combine d bu
		else DeleteEntry value d (combine (Entry(a,b,c,empty)) bu) 

fun ReturnValD (comb(x,st,cst)) empty = comb(none,st,cst)
	| ReturnValD (comb(x,st,cst)) (Entry(a,d,b,c)) =
			if (x = a) then 
				let val newst = DeleteEntry x st empty
				in (comb(b,newst,cst))
				end
			else ReturnValD (comb(x,st,cst)) c
	| ReturnValD Nothing _= (comb(none,empty,empty))

fun ReturnTypeD (comb(x,st,cst)) empty = (comb(~1,st,cst))
	| ReturnTypeD (comb(x,st,cst)) (Entry(a,d,b,c)) =
			if (x = a) then 
				let val newst = DeleteEntry x st empty
				in (comb(d,newst,cst))
				end
			else ReturnTypeD (comb(x,st,cst)) c
	| ReturnTypeD Nothing _ = (comb(~1,empty,empty))

fun ReturnValue (comb(x,st,cst)) empty = (comb("",st,cst))
	| ReturnValue (comb(x,st,cst)) (Entry(a,_,boolean(b),c)) = 
			if (x = a) then 
				let val newst = DeleteEntry x st empty
				in (comb(Bool.toString(b),newst,cst))
				end
			else ReturnValue (comb(x,st,cst)) c
	| ReturnValue (comb(x,st,cst)) (Entry(a,_,integer(b),c)) = 
			if (x = a) then 
				let val newst = DeleteEntry x st empty
				in (comb(Int.toString(b),newst,cst))
				end
			else ReturnValue (comb(x,st,cst)) c
	| ReturnValue (comb(x,st,cst)) (Entry(a,_,none,c)) = 
			if (x = a) then 
				let val newst = DeleteEntry x st empty
				in (comb("",newst,cst))
				end
			else ReturnValue (comb(x,st,cst)) c
	| ReturnValue Nothing _ = (comb("",empty,empty))

fun RetValue x empty = ""
	| RetValue x (Entry(a,_,integer(b),c)) =
			if (x = a) then Int.toString(b)
			else RetValue x c
	| RetValue x (Entry(a,_,boolean(b),c)) = 
			if (x = a) then Bool.toString(b)
			else RetValue x c
	| RetValue x (Entry(a,_,none,c)) =
			if (x = a) then ""
			else RetValue x c

datatype 'a hybrid = Null | cons of 'a * string SymbolT * string SymbolT * string list * 'a

fun tokenp Null = []
	| tokenp (cons(a,_,_,_,_)) = a

fun symbt Null = empty
	| symbt (cons(_,b,_,_,_)) = b
 
fun codep Null = []
	| codep (cons(_,_,_,c,_)) = c

fun compp Null = empty
	| compp (cons(_,_,d,_,_)) = d

fun allins Null = []
	| allins (cons(_,_,_,_,e)) = e

fun getinput a = a

fun getnewfile num file x =
		if (x < num) then getnewfile num (tl file) (x+1)
		else if (x = num) then (file) 
		else file	


fun Assignment (comb(ins,st,cst))  = 
	let val lhs = hd ins
			val rhs = hd (rev ins)
			val notempr = Lookup rhs cst
			val notempl = Lookup lhs cst
	in if (isSome (Int.fromString rhs) = true) then
				let val newst = AddEntry lhs 0 (integer(valOf (Int.fromString rhs))) st
				in comb(ins,newst,cst)
				end
		 else if (isSome (Bool.fromString rhs) = true) then
				let val newst = AddEntry lhs 1 (boolean(valOf (Bool.fromString rhs))) st
				in comb(ins,newst,cst)
				end
		 else
		 if notempr = true andalso notempl = false then 
				let val rhstype = ReturnType rhs cst
						val rhsact = RetAct rhs cst
					  val newst = AddEntry lhs rhstype rhsact st
				in comb(ins,newst,cst)
				end
		 else if notempr = false andalso notempl = false then
				let val rhstype = ReturnType rhs st
						val (comb(rhsval,newst,_)) = ReturnValD (comb(rhs,st,cst)) st
						val newwst = AddEntry lhs rhstype rhsval newst
				in comb(ins,newwst,cst)
				end
		else if notempr = true andalso notempl = true then
				let val rhstype = ReturnType rhs cst
						val rhsact = RetAct rhs cst
						val newst = AddValue lhs rhsact cst
				in comb(ins,st,cst)
				end
		else 
				let val rhstype = ReturnType rhs st
						val (comb(rhsval,newst,_)) = ReturnValD (comb(rhs,st,cst)) st
						val newwst = AddValue lhs rhsval cst
				in comb(ins,newst,newwst)
				end
	end
	| Assignment Nothing = (comb([],empty,empty))

val A = ["+","*","-","/","%"]
val B = ["||","&&"]
val R = ["<","<=","=",">",">=","<>"]

fun exists [] value = false
	| exists (h::t) value = 
		if (h=value) then true
		else true andalso exists t value

val constants = [integer(0),integer(1),boolean(true),boolean(false)]

fun Evaluate (comb(ins,st,cst)) = 
	let val oper = hd (tl ins)
			val oper1N = hd ins
			val oper2N = hd (rev ins)
	in if oper2N = "1" orelse oper2N = "0" orelse oper2N = "true" orelse oper2N = "false" then
			let val comb(a1,newst,_) = ReturnValD (comb(oper1N,st,cst)) st
			in if (exists A oper) = true then
					let val integer(oper1V) = a1
							val oper2V = valOf (Int.fromString(oper2N))
					in if oper = "+" then comb(integer(oper1V + oper2V),newst,empty)
						 else if oper = "-" then comb(integer(oper1V - oper2V),newst,empty)
						 else if oper = "*" then comb(integer(oper1V * oper2V),newst,empty)
					   else if oper = "/" then comb(integer(oper1V div oper2V),newst,empty)
					 	 else comb(integer(oper1V mod oper2V),newst,empty)
					end
				else if (exists B oper) = true then
					let val boolean(oper1V) = a1
							val oper2V = valOf (Bool.fromString(oper2N))
					in if oper = "||" then comb(boolean(oper1V orelse oper2V),newst,empty)
						 else comb(boolean(oper1V andalso oper2V),newst,empty)
					end
				else if (exists R oper) = true then
					let val integer(oper1V) = a1
							val oper2V = valOf (Int.fromString(oper2N))
					in if oper = "<" then comb(boolean(oper1V < oper2V),newst,empty)
						 else if oper = "<=" then comb(boolean(oper1V <= oper2V),newst,empty)
						 else if oper = "=" then comb(boolean(oper1V = oper2V),newst,empty)
						 else if oper = ">" then comb(boolean(oper1V > oper2V),newst,empty)
						 else if oper = ">=" then comb(boolean(oper1V >= oper2V),newst,empty)
						 else comb(boolean(not (oper1V = oper2V)),newst,empty)
					end
				else comb(none,newst,empty)
			end
			
		 else 
			let val comb(b1,newwst,_) = ReturnValD (comb(oper2N,st,cst)) st
					val comb(a1,newst,_) = ReturnValD (comb(oper1N,newwst,cst)) newwst
		 	in if a1 = none orelse b1 = none then comb(none,newst,empty)
				 else 
	 				if (exists A oper) = true then
						let val integer(oper1V) = a1
								val integer(oper2V) = b1
						in if oper = "+" then comb(integer(oper1V + oper2V),newst,empty)
						 else if oper = "-" then comb(integer(oper1V - oper2V),newst,empty)
						 else if oper = "*" then comb(integer(oper1V * oper2V),newst,empty)
					   else if oper = "/" then comb(integer(oper1V div oper2V),newst,empty)
					 	 else comb(integer(oper1V mod oper2V),newst,empty)
						end
					else if (exists B oper) = true then
						let val boolean(oper1V) = a1
								val boolean(oper2V) = b1
						in if oper = "||" then comb(boolean(oper1V orelse oper2V),newst,empty)
						 else comb(boolean(oper1V andalso oper2V),newst,empty)
						end
					else if (exists R oper) = true then
						let val integer(oper1V) = a1
								val integer(oper2V) = b1
						in if oper = "<" then comb(boolean(oper1V < oper2V),newst,empty)
						 else if oper = "<=" then comb(boolean(oper1V <= oper2V),newst,empty)
						 else if oper = "=" then comb(boolean(oper1V = oper2V),newst,empty)
						 else if oper = ">" then comb(boolean(oper1V > oper2V),newst,empty)
						 else if oper = ">=" then comb(boolean(oper1V >= oper2V),newst,empty)
						 else comb(boolean(not (oper1V = oper2V)),newst,empty)
						end
					else comb(none,newst,empty)
				end
	end
	| Evaluate Nothing = (comb(none,empty,empty))
	
	


fun EvalAndAssign (comb(ins,st,cst))  = 
	if (hd ins = "Comp") then
		let val comb(result,newwst,_) = Evaluate (comb (tl (tl ins),st,cst))
				val lhs = hd ins
				val newst = AddEntry lhs 1 result newwst
		in comb(ins,newst,cst)
		end	
	else 
		let val oper1 = hd (tl (tl ins))
				val lhstype = ReturnType oper1 st
				val comb(result,newwst,_) = Evaluate (comb (tl (tl ins),st,cst))  (* datatype of return is valu*)
				val lhs = hd ins
				val notempl = Lookup lhs cst
		in if notempl = true then
				let val newst = AddValue lhs result cst
				in comb(ins,st,newst)
				end
			 else 
				let val newst = AddEntry lhs lhstype result newwst
				in comb(ins,newst,cst)
				end
		end
	| EvalAndAssign Nothing = (comb([],empty,empty))
				
fun ExecuteInstruction (cons([],a,b,c,d)) h = (cons([],a,b,c,d))
	| ExecuteInstruction ins h = (*ins*)
	if (hd h = "read") then
		let val v = hd (tl h)
				val nextins =  (hd (tl (tokenp ins)))
				val variable = hd nextins
				val typeof = ReturnType variable (compp ins)
				val input = valOf (TextIO.inputLine(TextIO.stdIn))
				val inp = map str (explode input)
				val act = concat (rev (tl (rev inp)))
		in if (typeof = 1) then 
					let val inputb = valOf (Bool.fromString act)
							val newst = AddEntry v typeof (boolean(inputb)) (symbt ins)
					in (cons(tokenp ins,newst,compp ins,codep ins,allins ins))
					end
			 else 
					let val inputi = valOf (Int.fromString act)
							val newst = AddEntry v typeof (integer(inputi)) (symbt ins)
					in (cons(tokenp ins,newst,compp ins,codep ins,allins ins))
					end
		end
	else if (hd h = "write") then 
		let val (comb(a,c,_)) = ReturnValue (comb("IE",symbt ins,empty)) (symbt ins)
				val b = (codep ins) @ (a::[])
		in (cons(tokenp ins,c,compp ins,b,allins ins))
		end
	else if (hd h = "goto") then
		let val insnum = Int.fromString (hd (tl h))
				val insf =  (getnewfile (valOf(insnum)) (allins ins) 1 )
		in 
				if (insf = []) then (cons([],symbt ins,compp ins,codep ins,allins ins))
				else ExecuteFile (cons(insf,symbt ins,compp ins,codep ins,allins ins))
		end
	else if (hd h = "if") then
		let val (comb(result,newst,_)) = ReturnValue (comb("BE",symbt ins,empty)) (symbt ins)
		in if result = "false" then
			let val jumpl = Int.fromString (hd (rev h))
					val insf = (getnewfile (valOf(jumpl)) (allins ins) 1 )
			in ExecuteFile (cons(insf,newst,compp ins,codep ins,allins ins))
			end
			else ins
		end
	else if (length h = 3) then 
		let val (comb(_,newst,newcst)) = (Assignment (comb(h,symbt ins,compp ins)) )
		in cons(tokenp ins,newst,newcst,codep ins,allins ins)
		end
	else if (length h = 5) then 
		let val (comb(_,newst,newcst)) = (EvalAndAssign (comb(h,symbt ins,compp ins)))
		in cons(tokenp ins,newst,newcst,codep ins,allins ins)
		end
	else ins

		 
and ExecuteFile (cons([],records,comp,result,f)) = (cons([],records,comp,result,f))
	| ExecuteFile (cons(insf,records,comp,result,f)) = 
			let val (cons(inss,recp,compp,resp,fi)) = ExecuteInstruction (cons(insf,records,comp,result,f)) (hd insf)
			in if inss = [] then cons([],recp,compp,resp,fi)
				 else ExecuteFile (cons(tl inss,recp,compp,resp,fi))
			end
	| ExecuteFile Null = (cons([],empty,empty,[],[]))




fun fragment [] res = res
	| fragment (h::t) res = 
			let val n = String.tokens Char.isSpace h
			in fragment t (res @ (n::[]))
			end
		

fun Implement sourcename =
	let val code = executefile sourcename
			val cst = execST sourcename
			val codefra = fragment (code) []
			val final = ExecuteFile (cons(codefra,empty,cst,[],codefra))
	in (codep final)
	end


in Implement sourcename
end


fun InterpreterWrite inputfile execfile =
	let val a = Interpreter inputfile
			val b = writeLines (execfile, a)
	in b
	end

fun IRandExec inputfile ircodefile execfile=
	let val a = writeResult inputfile ircodefile
			val b = InterpreterWrite inputfile execfile
	in b
	end 



end


