//Student names and numbers:
//Guus van Lankveld		0629468
//Xiayang Hao			0892474

using CP;

//Input data
tuple Product {
	key int productId;
	string name;
}

tuple Demand {
	key string demandId;
	int productId;
	int quantity;
	int deliveryMin;
	int deliveryMax;
	float nonDeliveryVariableCost;
	int dueTime;
	float tardinessVariableCost;
}

tuple Resource {
	key string resourceId;
	int resourceNr;
	string setupMatrixId;
	int initialProductId;
}

tuple SetupResource {
	key string setupResourceId;
}

tuple StorageTank {
	key string storageTankId;
	string name;
	int quantityMax;
	string setupMatrixId;
	int initialProductId;
}

tuple Step {
	key string stepId;
	int productId;
	string setupResourceId;
}

tuple Precedence {
	string predecessorId;
	string successorId;
	int delayMin;
	int delayMax;
}

tuple Alternative {
	key string stepId;
	key int alternativeNumber;
	string resourceId;
	int fixedProcessingTime;
	float variableProcessingTime;
	int fixedProcessingCost;
	float variableProcessingCost;
}

tuple StorageProduction {
	key string prodStepId;
	key string storageTankId;
	string consStepId;
}

tuple Setup {
	key string setupMatrixId;
	key int fromState;
	key int toState;
	int setupTime;
	int setupCost;
}

tuple CriterionWeight {
	key string criterionId;
	float weight;
}

{Product} Products = ...;
{Demand} Demands = ...;
{Resource} Resources = ...;
{SetupResource} SetupResources = ...;
{StorageTank} StorageTanks = ...;
{Step} Steps = ...;
{Precedence} Precedences = ...;
{Alternative} Alternatives = ...;
{StorageProduction} StorageProductions = ...;
{Setup} Setups = ...;
{CriterionWeight} CriterionWeights = ...;

int lowestDeliveryMin = min(d in Demands) d.deliveryMin;
int highestDeliveryMax = max(d in Demands) d.deliveryMax;

//{Step} stepsForProduct[p in Products] = {s | s in Steps : s.productId == p.productId};

//Decision variables
dvar interval demand[d in Demands]
	optional
	in 0..d.deliveryMax
	size(0..(d.deliveryMax-d.deliveryMin));

//Each demand and each step for a demand which is scheduled. Since not every demand has an equal number of steps, the interval is optional
dvar interval demandStep[d in Demands][s in Steps]
	optional
	in lowestDeliveryMin..highestDeliveryMax
	size(
		min(a in Alternatives : a.stepId == s.stepId) (a.fixedProcessingTime + ftoi(round(d.quantity*a.variableProcessingTime)))
		..
		((max(sr in Setups : sr.toState == s.productId) sr.setupTime) + 
			max(a in Alternatives : a.stepId == s.stepId) (a.fixedProcessingTime + ftoi(round(d.quantity*a.variableProcessingTime))))
	);

//Alternatives for each step scheduled in 
dvar interval demandAlternative[d in Demands][a in Alternatives]
	optional
	in lowestDeliveryMin..highestDeliveryMax
	size (
		(a.fixedProcessingTime+ftoi(round(a.variableProcessingTime*d.quantity)))
		..
		((max(sr in Setups, s in Steps : sr.toState == s.productId && s.stepId == a.stepId) sr.setupTime)+
			(a.fixedProcessingTime+ftoi(round(a.variableProcessingTime*d.quantity))))
	);
	//Storagetank for each demand scheduled in 
dvar interval demandStoragetank[d in Demands][s in StorageTanks]
	optional
	in lowestDeliveryMin..highestDeliveryMax
	size (
		0
		..
		(max(sr in Setups : sr.setupMatrixId == s.setupMatrixId ) sr.setupTime)+
		(max(p in Precedences, st1 in Steps, st2 in Steps : st1.productId==d.productId&&
		st2.productId==d.productId&&st1.stepId==p.predecessorId&&st2.stepId==p.successorId ) p.delayMax) // (startOf(demandStep[d][st2])-endOf(demandStep[d][st1])))
	);
dvar interval demandStoragetank1[s in StorageTanks]
	optional
	in lowestDeliveryMin..highestDeliveryMax
	size (
		0
		..
		(max(sr in Setups : sr.setupMatrixId == s.setupMatrixId ) sr.setupTime)+
		(max(d in Demands,p in Precedences, st1 in Steps, st2 in Steps : st1.productId==d.productId&&
		st2.productId==d.productId&&st1.stepId==p.predecessorId&&st2.stepId==p.successorId ) p.delayMax) // (startOf(demandStep[d][st2])-endOf(demandStep[d][st1])))
	);
dvar sequence resources[r in Resources] 
	in all(d in Demands, s in Steps, a in Alternatives : 
			s.productId == d.productId && a.stepId == s.stepId && a.resourceId == r.resourceId) demandAlternative[d][a];
dvar sequence storagetank[s in StorageTanks] 
	in all(sp in StorageProductions, p in Precedences, s1 in Steps,s2 in Steps,d in Demands : 
			s1.productId == d.productId&&s2.productId == d.productId && p.predecessorId == s1.stepId &&p.successorId == s2.stepId&& p.predecessorId==sp.prodStepId&&p.successorId==sp.consStepId&&sp.consStepId==s.storageTankId) demandStoragetank[d][s];
		
//Expressions
dexpr int TotalFixedProcessingCost = 
	sum(d in Demands, a in Alternatives) presenceOf(demandAlternative[d][a])*a.fixedProcessingCost;

dexpr float TotalVariableProcessingCost = 
	sum(d in Demands, a in Alternatives) presenceOf(demandAlternative[d][a])*a.variableProcessingCost*d.quantity;

dexpr float TotalNonDeliveryCost = 
	sum(d in Demands) (1-presenceOf(demand[d]))*d.nonDeliveryVariableCost*d.quantity;
	
pwlFunction tardiness[d in Demands] = 
	piecewise{0->d.dueTime;d.tardinessVariableCost}(0,0);	
	          				
dexpr float TardinessCost[d in Demands] =
	endEval(demand[d], tardiness[d]);
	 
dexpr float TotalTardinessCost = 
	sum(d in Demands) TardinessCost[d]; 
	
dexpr float TotalSetupCost = 
	sum(d in Demands, a in Alternatives, r in Resources, s in Steps, su in Setups : 
			a.resourceId == r.resourceId && a.stepId == s.stepId && r.setupMatrixId == su.setupMatrixId &&
			su.fromState == r.initialProductId && su.toState == s.productId) 
			presenceOf(demandStep[d][s]) * su.setupCost;
	
cumulFunction StorageFulse[s in StorageTanks] = sum(d in Demands) pulse(demandStoragetank[d][s],d.quantity);
//Environment settings
execute {
  cp.param.Workers = 1;
  cp.param.TimeLimit = Opl.card(Demands); 
}

//Objective
minimize 
	TotalFixedProcessingCost + 
	TotalVariableProcessingCost + 
	TotalNonDeliveryCost +
	TotalTardinessCost + 
	TotalSetupCost;
	
//Constraints
subject to {

	//Demands cannot be finished before their deliveryMin time
	forall(d in Demands) {
		endOf(demand[d]) >= d.deliveryMin;
	}


	//All steps for a demand should be present when the demand itself is present
	forall(d in Demands, s in Steps : d.productId == s.productId) {
		//Old version. Not correct since this still allows demandStep[x][y] to be present  even if demand[x] is absent
		//(presenceOf(demand[d]) => presenceOf(demandStep[d][s]));
		
		(presenceOf(demand[d]) == presenceOf(demandStep[d][s]));
	}
	
	//No demand/step combination should be present when the step is not required for a demand
	forall(d in Demands, s in Steps : d.productId != s.productId) {
		!presenceOf(demandStep[d][s]);
	}
	
	//No overlap between steps on a single resource
	forall(r in Resources)
	  noOverlap(resources[r]);
	
	//Steps of a demand must be within the demand interval
	forall(d in Demands)
    	span(demand[d], all(s in Steps) demandStep[d][s]);
	
	//Demand step precedences
	forall(d in Demands, s1 in Steps, s2 in Steps) {
		forall(p in Precedences : (p.predecessorId == s1.stepId) && (p.successorId == s2.stepId)) {
			endBeforeStart(demandStep[d][s1], demandStep[d][s2], p.delayMin);
			
			//Maximal delay between steps
			startOf(demandStep[d][s2])-endOf(demandStep[d][s1]) <= p.delayMax;
 		}			
	}
	
	//Alternatives for a step
	forall(d in Demands, s in Steps) {
		alternative(demandStep[d][s], all(alt in Alternatives: alt.stepId==s.stepId) demandAlternative[d][alt]);
	}
	
	//Length of each alternative, including the setup time
	forall(d in Demands, a in Alternatives, r in Resources, s in Steps, su in Setups : 
				a.resourceId == r.resourceId && a.stepId == s.stepId && r.setupMatrixId == su.setupMatrixId &&
				su.fromState == r.initialProductId && su.toState == s.productId) {
		//Alternative is either not present or has length of processingtime+setuptime
		!presenceOf(demandAlternative[d][a]) || (
			lengthOf(demandAlternative[d][a]) == (
				a.fixedProcessingTime + ftoi(round(d.quantity*a.variableProcessingTime)) + (
					((s.setupResourceId != "NULL") && (r.setupMatrixId != "NULL")) * (su.setupTime)
				)
			)
		);
	}
	//Storage
		//No overlap of storage
	forall(s in StorageTanks)
	  noOverlap(storagetank[s]);
	  
	  
	  forall(sp in StorageProductions, p in Precedences, s1 in Steps,s2 in Steps,d in Demands,s in StorageTanks: 
			s1.productId == d.productId&&s2.productId == d.productId && p.predecessorId == s1.stepId &&p.successorId == s2.stepId&& 
			p.predecessorId==sp.prodStepId&&p.successorId==sp.consStepId&&sp.consStepId==s.storageTankId&&sp.storageTankId==s.storageTankId)
			 {
			 			//s.quantityMax- d.quantity>=0;
			 			StorageFulse[s]<=s.quantityMax;

			 }
	

//Post Processing


//Output
/*execute {
  	writeln("Total Non-Delivery Cost    : ", TotalNonDeliveryCost);
  	writeln("Total Processing Cost      : ", TotalProcessingCost);
  	writeln("Total Setup Cost           : ", TotalSetupCost);
  	writeln("Total Tardiness Cost       : ", TotalTardinessCost);
  	writeln();
  	writeln("Weighted Non-Delivery Cost : ", WeightedNonDeliveryCost);
  	writeln("Weighted Processing Cost   : ", WeightedProcessingCost);
  	writeln("Weighted Setup Cost        : ", WeightedSetupCost);
  	writeln("Weighted Tardiness Cost    : ", WeightedTardinessCost);
  	writeln();
     
  	for(var d in demandAssignments) {
 		writeln(d.demandId, ": [", 
 		        d.startTime, ",", d.endTime, "] ");
 		writeln("   non-delivery cost: ", d.nonDeliveryCost, 
 		        ", tardiness cost: " , d.tardinessCost);
  	} 
  	writeln();

 	for(var sa in stepAssignments) {
 		writeln(sa.stepId, " of ", sa.demandId, 
 		        ": [", sa.startTime, ",", sa.endTime, "] ", 
 		        "on ", sa.resourceId);
 		write("   processing cost: ", sa.procCost);
 		if (sa.setupCost > 0)
 		  write(", setup cost: ", sa.setupCost);
 		writeln();
 		if (sa.startTimeSetup < sa.endTimeSetup)
 			writeln("   setup step: [", 
 			        sa.startTimeSetup, ",", sa.endTimeSetup, "] ",
 			        "on ", sa.setupResourceId);   
  	}
  	writeln();
  
  	for(var sta in storageAssignments) {
 		if (sta.startTime < sta.endTime) {
 			writeln(sta.prodStepId, " of ", sta.demandId, 
 				" produces quantity ", sta.quantity,
 			    	" in storage tank ", sta.storageTankId,
 		    	     " at time ", sta.startTime, 
" which is consumed at time ", sta.endTime);	
}		
  	}	   
} */
}
