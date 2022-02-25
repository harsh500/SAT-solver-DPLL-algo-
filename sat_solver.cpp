// C++ program to implement an efficient SAT Solver using the DPLL algorithm

#include<bits/stdc++.h>
#define MAX_FILE_NAME_SIZE 500
#define ll long long int
using namespace std;

using namespace std::chrono;
 
ll num_vars;        //stores the number of variables in the input CNF formula

set<ll> model;      //stores te=he satisfying model of the formula if it is SAT


// utility function to display all the formulas
// to see if the code has read the file correctly
void display_formulas(vector<set<ll> > formulas)
{
    if(formulas.size() == 0) {
        cout << "Empty Formula!!\n";
    }
    vector<set<ll> >::iterator it1;
    set<ll>::iterator it2;
    for(it1 = formulas.begin(); it1 != formulas.end(); it1++) {
        for(it2 = (*it1).begin(); it2 != (*it1).end(); it2++) {
            cout <<*it2 << " ";
        }
        cout << "\n";
    }
    return;
}

// this function checks if the formulas has unit clauses and returns the set of unit clauses
vector<ll> unit_clause_check(vector<set<ll> >& clauses)
{
    vector<ll> singular_clauses;
    vector<set<ll> >::iterator itr;
    
    for(itr = clauses.begin(); itr != clauses.end(); itr++) {
        if((*itr).size() == 1) {
            singular_clauses.push_back(*((*itr).begin()));
        }
    }
   
    return singular_clauses;
}

// this function checks if the formula has pure literals and returns them
vector<ll> pure_literal_check(vector<set<ll> >& clauses)
{
    bool pos[num_vars];
    bool neg[num_vars];
    vector<ll> pure_literals;
    for(ll i = 0; i < num_vars; i++) {
        pos[i] = false;
        neg[i] = false;
    }

    for(vector<set<ll> >::iterator itr = clauses.begin(); itr != clauses.end(); itr++) {
        for(set<ll>::iterator it = itr->begin(); it != itr->end(); it++) {
            if(*it > 0) {
                pos[(*it)-1] = true;
            }
            else {
                neg[-1*(*it)-1] = true;
            }
        }
    }

    for(ll i = 0; i < num_vars; i++) {
        if(pos[i] == true && neg[i] == false) {
            pure_literals.push_back(i+1);
        }
        else if(neg[i] == true && pos[i] == false){
            pure_literals.push_back(-i-1);
        }
    }
  
    return pure_literals;
}

// this function removes the pure literals and simplifies the formula
void pure_literal_assign(vector<set<ll> >& clauses, vector<ll>& sing_clauses)
{
    vector<ll> pure_literals = pure_literal_check(clauses);
    vector<ll>::iterator itr;
    if(clauses.size() == 0) return ;  
      
    while(pure_literals.size() > 0) {
        
        for(itr = pure_literals.begin(); itr != pure_literals.end(); itr++) {
            sing_clauses.push_back(*itr);
            clauses.erase(remove_if(clauses.begin(),clauses.end(),[itr](set<ll> i){return i.find(*itr)!=i.end();}),clauses.end());
            
        }
        
        pure_literals = pure_literal_check(clauses);

    }
}

// this function implements repeated unit propagation
void unit_propagate(vector<set<ll> >& clauses, vector<ll>& sing_clauses)
{
    vector<ll> singular_clauses = unit_clause_check(clauses);
    vector<ll>::iterator itr;
    while(singular_clauses.size() > 0) {
        if(clauses.size() == 0) return ;

        vector<ll>temp_cl;
        for(itr = singular_clauses.begin(); itr != singular_clauses.end(); itr++) {
            sing_clauses.push_back(*itr);
            
            clauses.erase(remove_if(clauses.begin(),clauses.end(),[itr](set<ll> i){return i.find(*itr)!=i.end();}),clauses.end());
            for(vector<set<ll> >::iterator it = clauses.begin(); it != clauses.end(); it++) {
                if((*it).find(-1*(*itr)) != (*it).end()) {
                   // cout << "Erasing literal " << -1*(*itr) << "\n"; 
                    (*it).erase((*it).find(-1*(*itr)));
                    if(it->size() == 0) return;
                    if(it->size() == 1) temp_cl.push_back(*(it->begin()));
                }
             }
            
        }
        singular_clauses = temp_cl;

    }

}


// this function find the literal occurring max times in the formula
ll max_occurrence(vector<set<ll> >& clauses)
{
    map<ll, ll> cnt;
    cnt[0] = 0;
    for(vector<set<ll> >::iterator itr = clauses.begin(); itr != clauses.end(); itr++) {
        for(set<ll>::iterator it = itr->begin(); it != itr->end(); it++) {
            cnt[*it]++;
        }
    }
    ll max_lit = 1;
    map<ll, ll>::iterator itr;
    for(ll i = -1*num_vars; i <= num_vars; i++) {
        if(cnt[max_lit] + cnt[-1*max_lit]< cnt[i] + cnt[-i]) {
            max_lit = i;
        }
    }
    if(cnt[max_lit] > cnt[-1*max_lit])
        return max_lit;
    else return -1*max_lit;
} 

ll cnt = 0;     //to keep track of no of calls made to DPLL

// DPLL function, return true for SAT, false for UNSAT
bool DPLL(vector<set<ll> >& clauses)
{
    
    //check if any clause in the formula is empty
    for(vector<set<ll> >::iterator itr = clauses.begin(); itr != clauses.end(); itr++) 
    {
        if(itr->size() == 0) {
            return false;
        }
    }

    if(clauses.size() == 0) return true;
    
    vector<ll> singular_clauses;
    cnt++;
    // **********Uncomment the following line to see the no of DPLL calls periodically*******************
    //if(cnt % 1000 == 0) cout << "DPLL called! " << cnt << "\n";
   
    unit_propagate(clauses, singular_clauses);      //function call for unit propagation
    
    pure_literal_assign(clauses, singular_clauses);     //function call for pure literal assignment

    // if the formula is empty we return SAT and the model
    if(clauses.size() == 0) {
        for(vector<ll>::iterator itr = singular_clauses.begin(); itr != singular_clauses.end(); itr++) {
            model.insert(*itr);
        }
    
        return true;
    }
    // if any of the clauses in the formula is empty, we return UNSAT
    for(vector<set<ll> >::iterator itr = clauses.begin(); itr != clauses.end(); itr++) 
    {
        if(itr->size() == 0) {
            return false;
        }
    }

    ll lit = max_occurrence(clauses);   // to find the literal of max occurrence, we will assume it now
    set<ll> s1, s2;
    s1.insert(lit);
    s2.insert(-1*lit);
    vector<set<ll> > clauses1, clauses2;
    for(vector<set<ll> >::iterator itr = clauses.begin(); itr != clauses.end(); itr++) {
        clauses1.push_back(*itr);
        clauses2.push_back(*itr);
    }
    
    clauses1.push_back(s1);     //clauses /\ {lit}
    clauses2.push_back(s2);     //clauses /\ {~lit}
    
    if(DPLL(clauses1)) {
        for(vector<ll>::iterator itr = singular_clauses.begin(); itr != singular_clauses.end(); itr++) {
            model.insert(*itr);
        }
        model.insert(lit);

        return true;
    }
    else if(DPLL(clauses2)) {
        for(vector<ll>::iterator itr = singular_clauses.begin(); itr != singular_clauses.end(); itr++) {
            model.insert(*itr);
        }
        model.insert(-1*lit);
        return true;

    }
    else return false;
}

// This function checks that the model returned by the solver is right if the formula is SAT
void check(vector<set<ll> >& clauses,ll num_clauses){
    vector<ll>interpretations(num_vars+1);
    for(ll i = 1; i <= num_vars; i++) {
            if(model.find(i) != model.end()) interpretations[i]=i;
            else if(model.find(-1*i) != model.end()) interpretations[i]=-i;
            else interpretations[i]=i;
        }
    ll cnt=0;
    ll f=0;
    for(ll j=0;j<num_clauses;j++){
        f=0;
        for(auto k:clauses[j]){
            if(k<0){
                if(interpretations[-k]==k){
                    cnt++;
                    f=1;
                    break;
                }
            }
            else{
                if(interpretations[k]==k){
                    cnt++;
                    f=1;
                    break;
                }
            }
        }
        if(f==0){
            cout<<j<<"\n";
            for(auto k:clauses[j]){
                cout<<k<<" ";            
            }
            cout<<"\n";
        }
    }
    if(cnt==num_clauses){
        cout<<"Done";
    }
    else{
        cout<<"wrong";
    }
}


int main()
{
    auto start = high_resolution_clock::now();      //setup the clock
    char fileName[MAX_FILE_NAME_SIZE+1] = "testcases/testcase_1.cnf";    //input file
    FILE* fp = fopen(fileName, "r");
    char ch;
    ll  num_clauses;

    // Now reading from the .cnf file
    fscanf(fp, "%c", &ch);
    while(ch != 'p' && ch =='c') {
        while(ch != '\n') {
            fscanf(fp, "%c", &ch);
        }
        fscanf(fp, "%c", &ch);
    }
    // Now reading from the .cnf file
    fscanf(fp, " cnf %lld %lld", &num_vars, &num_clauses);
    ll i;
    vector<set<ll> > clauses(num_clauses);
    for(i = 0; i < num_clauses; i++) {
        ll temp;
        fscanf(fp, "%lld", &temp);
        while(temp != 0) {
            clauses[i].insert(temp);
            fscanf(fp, "%lld", &temp);
        }
    }
   vector<set<ll> > clausescopy=clauses;
    if(DPLL(clauses)) {
        cout << "SAT\n";
        set<ll>::iterator itr;
        cout << "* * * * * * * * * * * * * * * * * * * * * * * "<<"\n";
        for(i = 1; i <= num_vars; i++) {
            if(model.find(i) != model.end()) cout << i << " ";
            else if(model.find(-1*i) != model.end()) cout << -i << " ";
            else cout << i << " ";
            
        }

        cout << 0 << " \n";
        /*
        check(clausescopy,num_clauses);     // if the formula is SAT, checks if the model is right
        */
    }
    else cout << "UNSAT\n";
    auto stop = high_resolution_clock::now();
    auto duration = duration_cast<microseconds>(stop - start);
 
    cout << "* * * * * * * * * * * * * * * * * * * * * * * "<<"\n";
    cout << "Time taken: ";
    cout << duration.count()/1000000.000000 <<" seconds" << endl;   
    
    return 0;
}