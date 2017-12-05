import java.io.BufferedReader;
import java.io.FileReader;
import java.io.InputStreamReader;
import java.util.Iterator;
import java.util.Vector;

public class Main {

	public static void main(String[] args) {
		
		String str, name;
		boolean negation;
		CNFClause knowledgeBase = new CNFClause();
		Vector<CNFSubClause> subClauses = new Vector<CNFSubClause>();
		CNFSubClause testSub = new CNFSubClause();
		
		try {
			BufferedReader kb = new BufferedReader(new FileReader("C:\\tmp\\kb.txt"));
			System.out.println("Type CNF sub clause to be tested");
			BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
			
			try {
				String s = br.readLine();
				if(s.contains(" ^ ")) {
					String[] testClause = s.split(" ^ ");
					for(String sub : testClause) {
						String[] test = sub.split(" v ");
						for(String l: test) {
							String[] lit = l.split("-");
							name = lit[0];
							negation = Boolean.valueOf(lit[1]);
							testSub.getLiterals().add(new Literal(name, negation));
						}
					}
				}
				
				
				
				while ((str = kb.readLine()) != null) {
					CNFSubClause subClause = new CNFSubClause();
					String[] literals = str.split(" v ");
					for(String l: literals) {
						String[] lit = l.split("-");
						name = lit[0];
						negation = Boolean.valueOf(lit[1]);
						subClause.getLiterals().add(new Literal(name, negation));
					}
					subClauses.add(subClause);
					
				}
			}
			finally {
            	kb.close();
            	br.close();
            }
			
			knowledgeBase.theClauses = subClauses;
		}
		catch(Exception e) {
			System.out.println(e);
		}
			
		System.out.println("----------------------------------------------------");
        System.out.println();

        //Running resolution
        boolean b = PL_Resolution(knowledgeBase, testSub);
        testSub.print();
        System.out.println("is " + b);
	}
	
	//The resolution algorithm
    public static boolean PL_Resolution(CNFClause KB, CNFSubClause testClause)
    {
        //We create a CNFClause that contains all the clauses of our Knowledge Base
        CNFClause clauses = new CNFClause();
        clauses.getSubclauses().addAll(KB.getSubclauses());
        
        //...plus a clause containing the negation of the literal we want to prove
        CNFSubClause testCopy = new CNFSubClause();
        Iterator<Literal> iter = testClause.getLiteralsList();
        while(iter.hasNext()) {
        	Literal tmp = iter.next();
        	testCopy.getLiterals().add(new Literal(tmp.getName(), !tmp.getNeg()));
        }
        
        clauses.getSubclauses().add(testCopy);

        System.out.println("We want to prove...");
        testClause.print();

        boolean stop = false;
        int step = 1;
        //We will try resolution till either we reach a contradiction or cannot produce any new clauses
        while(!stop)
        {
            Vector<CNFSubClause> newsubclauses = new Vector<CNFSubClause>();
            Vector<CNFSubClause> subclauses = clauses.getSubclauses();

            System.out.println("Step:" + step);
            step++;
            //For every pair of clauses Ci, Cj...
            for(int i = 0; i < subclauses.size(); i++)
            {
                CNFSubClause Ci = subclauses.get(i);

                for(int j = i+1; j < subclauses.size(); j++)
                {
                    CNFSubClause Cj = subclauses.get(j);

                    //...we try to apply resolution and we collect any new clauses
                    Vector<CNFSubClause> new_subclauses_for_ci_cj = CNFSubClause.resolution(Ci, Cj);

                    //We check the new subclauses...
                    for(int k = 0; k < new_subclauses_for_ci_cj.size(); k++)
                    {
                        CNFSubClause newsubclause = new_subclauses_for_ci_cj.get(k);

                        //...and if an empty subclause has been generated we have reached contradiction; and the literal has been proved
                        if(newsubclause.isEmpty()) 
                        {   
                            System.out.println("----------------------------------");
                            System.out.println("Resolution between");
                            Ci.print();
                            System.out.println("and");
                            Cj.print();
                            System.out.println("produced:");
                            System.out.println("Empty subclause!!!");
                            System.out.println("----------------------------------");
                            return true;
                        }
                        
                        //All clauses produced that don't exist already are added
                        if(!newsubclauses.contains(newsubclause) && !clauses.contains(newsubclause))
                        {
                            System.out.println("----------------------------------");
                            System.out.println("Resolution between");
                            Ci.print();
                            System.out.println("and");
                            Cj.print();
                            System.out.println("produced:");
                            newsubclause.print();
                            newsubclauses.add(newsubclause);
                            System.out.println("----------------------------------");
                        }
                    }                           
                }
            }
            
            boolean newClauseFound = false;

            //Check if any new clauses were produced in this loop
            for(int i = 0; i < newsubclauses.size(); i++)
            {
                if(!clauses.contains(newsubclauses.get(i)))
                {
                    clauses.getSubclauses().addAll(newsubclauses);                    
                    newClauseFound = true;
                }                        
            }

            //If not then Knowledge Base does not logically infer the literal we wanted to prove
            if(!newClauseFound)
            {
                System.out.println("Not found new clauses");
                stop = true;
            }   
        }
        return false;
    }    

}
