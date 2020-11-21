\insert 'Unify.oz'
\insert 'Util.oz'

declare Counter MainUtil Main Nop SemanticStack Push Pop IsEmpty SemanticStatement Statement Environment Match Conditional GetEnv File Prog
    Statement = {NewCell nil}
    Environment = {NewCell nil}
    SemanticStack = {NewCell nil}
    Counter = {NewCell 0}
    SemanticStatement = statement(st:Statement env:Environment)
   
    %Change Prog according to AST and run file.
    Prog = [var ident(w) 
            [var ident(x) 
              [var ident(y) 
                [
                  [bind ident(w) literal(10)]
                  [bind ident(x) [record literal(a)[[literal(1) ident(y)][literal(2) ident(w)]]]]
                  [bind ident(y) literal(5)]   
                  [match ident(x) [record literal(a)[[literal(1) ident(z)][literal(2) ident(p)]]] 
                    [var ident(t) [nop]] [var ident(f) [nop]]]   
                ]
              ]
            ]] 
   


    %Stack Functions
    fun {Pop S} case @S of nil then nil [] X|X1 then S:=X1 X end end
    proc {Push S E} S:=E|@S end
    fun {IsEmpty S} @S==nil end

    %Nop
    proc {Nop}
       {Main}
    end
    
    %This function keeps track of the new variables introduced in SAS. It also ensures that everytime 
    % a unique variable is introduced
    fun {GetNewVar}
       Counter:=@Counter+1
       {AddKeyToSAS @Counter}
       @Counter
    end

   
    %Returns the copy of the environment with variable N. It takes care of repitions and makes sure to replave them
    % Don't directly call this function for new identifiers
    fun {CopyEnv L N}
       %{Browse N#L}
       case L of
          nil then N|nil
       [] X|Xr then if X.1==N.1 then {CopyEnv Xr N} else X|{CopyEnv Xr N} end
       end
    end

    % Performs the adj operation on environment. X is the new identifier of the form ident(Z)
    fun {AdjEnv L X}
       %{Browse x#L}
       case X of
          ident(Y) then {CopyEnv L [ident(Y) {GetNewVar}]}
       end
    end

    % Procedure to handle the var command.
    % T = statement(st:[ident(newVariable) <Rest of the statement>] env:E)
    proc {Var T}
        %  {Browse T.st.1#T.st.2.1}
        case T.st of
          nil then {Main}
          [] X|Xr then {Push SemanticStack statement(st:Xr env:{AdjEnv T.env X})} {Main}
        end
    end

    % Procedure to handle the bind command.
    proc {Bind T}
       local X Y in
          X = {FindX T.env T.st.1}
          Y = {FindX T.env T.st.2.1}
          %{Browse T.env#X#T.st.2.1}
          %{Browse {Dictionary.keys SAS}}
          %{Browse {Dictionary.items SAS}}
          %{Browse {RetrieveFromSAS 1}}
          %{Browse 'In Bind, before unify'}
          local Q in
             case T.st.2.1
             of Z|Zr then if Z==proc1 then Q=T.st.2.1#{ProcRet T.st.2.1 T.env} else Q=T.st.2.1 end
             else
                Q=T.st.2.1
             end
          %{BindRefToKeyInSAS X Y}
             %{Browse T.st.1#Q#T.env#'Hi yes'}
             {Unify T.st.1 Q T.env}
             {Main}
          end
          %{Browse X}
       end
    end

    % T is of the form statement(st:[ident(X) s1 s2] env:E)
    proc {Conditonal T}
      local S in
        S = {RetrieveFromSAS {FindX T.env T.st.1}}
        case S
        of equivalence(X) then {Exception.'raise' variableUnbound(conditional)}
        [] t then {Push SemanticStack statement(st:T.st.2.1 env:T.env)} {Main}
        [] f then {Push SemanticStack statement(st:T.st.2.2.1 env:T.env)} {Main}
        end 
      end
    end

    fun {Find V T1 T2}
       case T1#T2
       of nil#nil then notFound
       [](X|Xr)#(Y|Yr) then if Y==value(V) then X else {Find V Xr Yr} end
       end
    end

    fun {GetSASVarFromVal V}
       local T1 T2 in
    T1 = {Dictionary.keys SAS}
    T2 = {Dictionary.items SAS}
    {Find V T1 T2}
       end
    end
 
    fun {AddEnvPattern Xs P E}
        case Xs
        of nil then E
  [] X|Xr then
     case X.2.1
     of ident(Z) then {AddEnvPattern Xr P {CopyEnv E [{GetIdentRecord P X.1} {FindX E X.2.1}]}}
     [] equivalence(Z) then {AddEnvPattern Xr P {CopyEnv E [{GetIdentRecord P X.1} Z]}}
     else
        local T T2 in
     T2 = {GetSASVarFromVal X.2.1}
     if T2 == notFound
     then T = {AdjEnv E {GetIdentRecord P X.1}} {Unify {GetIdentRecord P X.1} X.2.1 T}  {AddEnvPattern Xr P T}
     else T = {CopyEnv E [{GetIdentRecord P X.1} T2]}  {AddEnvPattern Xr P T}
     end
        end
     end
        end
    end

    % T is of the form statement(st:[ident(X) s1 s2] env:E)
    proc {Match T}
      local S P in
         S = {RetrieveFromSAS {FindX T.env T.st.1}}
   P = T.st.2.1
   %{Browse T.st.1}
   %{Browse s#S#p#P}
   case S
   of equivalence(X) then {Exception.'raise' variableUnbound(match)}
   [] X then case X.2.1#P.2.1
        of (literal(Y))#(literal(Z)) then
           if (Y==Z andthen {Len X.2.2.1} == {Len P.2.2.1}) andthen {L1SubsetL2 P.2.2.1 X.2.2.1}
           then {Push SemanticStack statement(st:T.st.2.2.1 env:{AddEnvPattern X.2.2.1 P.2.2.1 T.env})}{Main}
           else {Push SemanticStack statement(st:T.st.2.2.2.1 env:T.env)} {Main}
           end
        end
   end
      end
    end


    fun {GetClosure S E Local}
       case S
       of ident(Z) then if {ListExistClosure Local S} then nil else [S {FindX E S}]|nil end
       [] X|Xr then {Merge {GetClosure X E Local} {GetClosure Xr E Local}}
       else nil
       end
    end

    fun {ProcRet S E}
       {GetClosure S.2.2.1 E S.2.1}
    end

    proc {Proc S E}
       local CloEnv in
          CloEnv = {GetClosure S.2.2.1 E S.2.1}
          %{Browse cloEnv#CloEnv}
          %{Browse value([S CloEnv])}
       end
    end

    % Note does not work for literals i.e. the arguments of the procedure has to be an identifier.It can't be a value
    fun {GenEnv L1 L2 E}
       %{Browse 'Hi'}
       %{Browse L1#L2}
       case L1#L2
       of nil#nil then nil
       [] (X|Xr)#(Y|Yr) then [X {FindX E Y}]|{GenEnv Xr Yr E}
       end
    end

    proc {Apply T}
       local X E in
          X = {RetrieveFromSAS {FindX T.env T.st.1}}
          {Browse T}
          case X
          of (proc1|PVal)#Closure then E={Merge {Merge {GenEnv PVal.1 T.st.2 T.env} Closure} [T.st.1 X] }
          end
          %{Browse 'In Proc'}
          case X
          of V#C then {Push SemanticStack statement(st:V.2.2.1 env:E)}
          end
          %{Browse E}
          {Main}
       end
    end

    % X,Y,Z are of the form ident(x) and E is the environment
    proc {Add X Y Z E}
       local T1 T2 in
    T1 = {RetrieveFromSAS {FindX E X}}
    T2 = {RetrieveFromSAS {FindX E Y}}
       case T1#T2
       of (literal(N1))#(literal(N2)) then {Push SemanticStack statement(st:[bind Z literal(N1+N2)] env: E)} {Main}
       else
    {Exception.'raise' variableUnbound(add)}
       end
       end
    end

    proc {Product X Y Z E}
       local T1 T2 in
    T1 = {RetrieveFromSAS {FindX E X}}
    T2 = {RetrieveFromSAS {FindX E Y}}
       case T1#T2
       of (literal(N1))#(literal(N2)) then {Push SemanticStack statement(st:[bind Z literal(N1*N2)] env: E)} {Main}
       else
    {Exception.'raise' variableUnbound(add)}
       end
       end
    end

    % S = Stack and E = Environment
    proc {MainUtil S E}
    case S.1 of
       nil then {Main}
    [] nop then {Nop}
    [] var then  {Var statement(st:S.2 env:E)}
    [] record then skip
    [] bind then  {Bind statement(st:S.2 env:E)}
    [] conditional then {Browse conditional} {Conditonal statement(st:S.2 env:E)}
    [] match then {Browse match} {Match statement(st:S.2 env:E)}
    [] apply then {Browse apply} {Apply statement(st:S.2 env:E)}
    [] proc1 then {Browse proc1} {Proc S E}% {Proc statement(st:S.2 env:E)}
    [] add then {Browse add} {Add S.2.1 S.2.2.1 S.2.2.2.1 E} 
    [] mul then {Browse product} {Product S.2.1 S.2.2.1 S.2.2.2.1 E}
    [] Y|Yr then {Push SemanticStack statement(st:S.2 env:E)} {Push SemanticStack statement(st:S.1 env:E)} {Main}
    end
    end
 
    proc {Main}
      local T in
   T = {Pop SemanticStack}
   if T \= nil andthen T.st \= nil then
        {Browse '------------------------------------'}
      {Browse 'statement:'}
      {Browse T.st}
      {Browse 'Environment for this statement i.e. before execution of this statement:'}
      {Browse T.env}
      {Browse 'SAS before executing this statement:'}
      {Browse {Zip {Dictionary.keys SAS} {Dictionary.items SAS}}}
      %{File write(vs:[1 2 3 4 5]#{Dictionary.keys SAS}#{Dictionary.items SAS}#'\n')}
   end
   
   
          case T of
            nil then skip
            [] statement(st:X env:E) then if X==nil then {Main} else {MainUtil X E} end
          end
      end
    end
   {Push SemanticStack statement(st:Prog env:nil)}
    {Main}
    {Browse '------------------------------------'}
    {Browse 'Final SAS State'}
    {Browse {Zip {Dictionary.keys SAS} {Dictionary.items SAS}}}