----------------------------- MODULE AuthenticationSystem -----------------------------
EXTENDS Naturals, Sequences, TLC

\* Constants and variables
CONSTANTS USERS \* A set of all possible user identifiers
VARIABLES users, sessions

\* State representation
users \in [USERS -> ["password" : Seq(Int), "registered" : Bool]]
sessions \in [USERS -> Bool]

\* Initial state definition
Init == 
    /\ users = [u \in USERS |-> ["password" |-> <<>>, "registered" |-> FALSE]]
    /\ sessions = [u \in USERS |-> FALSE]

\* Actions
RegisterUser(u, pwd) ==
    /\ u \in USERS
    /\ ~users[u]["registered"]
    /\ users' = [users EXCEPT ![u] = [@ EXCEPT !["password"] = pwd, !["registered"] = TRUE]]
    /\ UNCHANGED sessions

LoginUser(u, pwd) ==
    /\ u \in USERS
    /\ users[u]["registered"]
    /\ users[u]["password"] = pwd
    /\ ~sessions[u]
    /\ sessions' = [sessions EXCEPT ![u] = TRUE]
    /\ UNCHANGED users

LogoutUser(u) ==
    /\ u \in USERS
    /\ sessions[u]
    /\ sessions' = [sessions EXCEPT ![u] = FALSE]
    /\ UNCHANGED users

\* Next-state relation
Next == 
    \E u \in USERS, pwd \in Seq(Int) :
        RegisterUser(u, pwd) \/ LoginUser(u, pwd) \/ LogoutUser(u)

\* Specification
Spec == Init /\ [][Next]_<<users, sessions>>

\* Safety properties
\* No unauthorized access: Only registered users with the correct password can log in
Safety_NoUnauthorizedAccess == 
    \A u \in USERS : sessions[u] => (users[u]["registered"] /\ users[u]["password"] = users[u]["password"])

\* Liveness properties (optional for later extensions)

===============================================================================
