//Student names and numbers:
//Guus van Lankveld		0629468		g.v.lankveld@student.tue.nl
//Xiayang Hao			0892474		x.hao@student.tue.nl

/*REMOVE THIS BEFORE SUBMITTING TO TEACHER:

- Say something about setup costs for storage tank not being used
- Explain implications in report when they are used.

*/


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

//Used in the old dvar demandStep[d in Demands][s in Steps]
//int lowestDeliveryMin = min(d in Demands) d.deliveryMin; 
//int highestDeliveryMax = max(d in Demands) d.deliveryMax;


//Decision variables
dvar interval demand[d in Demands]
	optional
	in 0..d.deliveryMax
	size(0..d.deliveryMax);

tuple DemandStep {
	Demand demand;
	Step step;
}

/*//Each demand and each step for a demand which is scheduled. Since not every demand has an equal number of steps, the interval is optional
dvar interval demandStep[d in Demands][s in Steps]
	optional
	in lowestDeliveryMin..highestDeliveryMax
	size(
		min(a in Alternatives : a.stepId == s.stepId) (a.fixedProcessingTime + ftoi(round(d.quantity*a.variableProcessingTime)))
		..
		((max(sr in Setups : sr.toState == s.productId) sr.setupTime) + 
			max(a in Alternatives : a.stepId == s.stepId) (a.fixedProcessingTime + ftoi(round(d.quantity*a.variableProcessingTime))))
);*/

{DemandStep} DemandSteps = {<d, s> | d in Demands, s in Steps : d.productId == s.productId};

//Each demand and each step for a demand which is scheduled. Since not every demand needs to be scheduled, the interval is optional
dvar interval demandStep[<d,s> in DemandSteps]
	optional
	in 0..d.deliveryMax
	size(
		min(a in Alternatives : a.stepId == s.stepId) (a.fixedProcessingTime + ftoi(floor(d.quantity*a.variableProcessingTime)))
		..
		(max(a in Alternatives : a.stepId == s.stepId) (a.fixedProcessingTime + ftoi(ceil(d.quantity*a.variableProcessingTime))))
	);

//Alternatives for each step scheduled in demandSteps
tuple DemandAlternative{
	Demand d;
	Alternative a;
}

{DemandAlternative} DemandAlternatives ={<d,a>|d in Demands, s in Steps, a in Alternatives : 
			s.productId == d.productId && a.stepId == s.stepId};		
			
dvar interval demandAlternative[<d,a> in DemandAlternatives]
	optional
	in 0..d.deliveryMax
	size (
		a.fixedProcessingTime+ftoi(round(a.variableProcessingTime*d.quantity))
	);
	
{int} ProductIds = {p.productId | p in Products};

//int setupCostArray[Resources][ProductIds][ProductIds];
//execute {
//  for(var r in Resources) {
//    for(var s in Setups) {
//      setupCostArray[r][s.fromState][s.toState] = 
//        s.setupCost;
//    }				  
//  }
//} 

int setupCostArray[r in Resources][p1 in ProductIds union {- 1}][p2 in ProductIds] = 
	sum( <r.setupMatrixId, p1, p2, setupTime, setupCost > in Setups) setupCost;
	
int setupTimeArray[r in Resources][p1 in ProductIds union {- 1}][p2 in ProductIds] = 
	sum( <r.setupMatrixId, p1, p2, setupTime, setupCost > in Setups) setupTime;
	
dvar interval setups[<d,a> in DemandAlternatives]
	optional
	in 0..d.deliveryMax
	size (
		(min(su in Setups, r in Resources, s in Steps : 
			s.stepId == a.stepId && r.resourceId == a.resourceId && su.toState == s.productId) su.setupTime)
		..
		(max(su in Setups, r in Resources, s in Steps : 
			s.stepId == a.stepId && r.resourceId == a.resourceId && su.toState == s.productId) su.setupTime)
	);
	
tuple TransitionTime {
	int fromProduct;
	int toProduct;
	int setupTime;
}

{TransitionTime} ResourceTransitionTimes[r in Resources] = {
	<fromProduct, toProduct, setupTime> | 
	<setupMatrixId, fromProduct, toProduct, setupTime, setupCost> in Setups : 
	r.setupMatrixId == setupMatrixId
};

tuple DemandAlternativeResource {
	DemandAlternative demandAlternative;
	Resource resource;
}

{DemandAlternativeResource} DemandAlternativeResources = {
	<<d,a>, r> | <d,a> in DemandAlternatives, r in Resources : a.resourceId == r.resourceId
};
	
dvar sequence resources[r in Resources] 
	in all(<<d,a>, r> in DemandAlternativeResources) demandAlternative[<d,a>] 
	types all(<<d,a>, r> in DemandAlternativeResources) d.productId;
	
{TransitionTime} StorageTransitionTimes[r in StorageTanks] = {
	<fromProduct, toProduct, setupTime> | 
	<setupMatrixId, fromProduct, toProduct, setupTime, setupCost> in Setups : 
	r.setupMatrixId == setupMatrixId
};
	
dvar interval storageSteps[<d, ps> in DemandSteps]
	optional
	in 0..d.deliveryMax;
	
tuple DemandStorage {
  Demand demand;
  StorageProduction storageProduction;
}

{DemandStorage} DemandStorages =
{<d,sp> | d in Demands, sp in StorageProductions, st in Steps 
       : sp.prodStepId == st.stepId && st.productId == d.productId};

dvar interval storageAltSteps[<d,sp> in DemandStorages]
	optional
	in 0..d.deliveryMax;

statefunction tankState[r in StorageTanks] with StorageTransitionTimes[r];

dexpr int resourceTypeOfPrev[<d,a> in DemandAlternatives] =
	typeOfPrev(
		resources[item(Resources, <a.resourceId>)], 
		demandAlternative[<d,a>], 
		item(Resources, <a.resourceId>).initialProductId,
		-1
	);

//Old code, used in the old storage setup constraint calculation
/*tuple DemandStorageProduct {
	DemandStorage ds;
	Product fromProduct;
	Product toProduct;
}

{DemandStorageProduct} DemandStorageProducts = {
	<<d, sp>, p1, p2> | <d, sp> in DemandStorages, p1 in Products, p2 in Products, s1 in Steps, s2 in Steps : 
	sp.prodStepId == s1.stepId && sp.consStepId == s2.stepId && s1.productId == p1.productId && s2.productId == s2.productId
};*/

cumulFunction storageTankUsage[r in StorageTanks] =
(sum(<d,sp> in DemandStorages 
   : sp.storageTankId == r.storageTankId)
   pulse(storageAltSteps[<d,sp>], d.quantity));
		
//Expressions
//dexpr int TotalFixedProcessingCost = 
//	sum(<d,a> in DemandAlternatives) presenceOf(demandAlternative[<d,a>])*a.fixedProcessingCost;
//
//dexpr float TotalVariableProcessingCost = 
//	sum(<d,a> in DemandAlternatives) presenceOf(demandAlternative[<d,a>])*a.variableProcessingCost*d.quantity;

//should be the same but get worse result
//dexpr float TotalProcessingCost = 
//	sum(<d,a> in DemandAlternatives) presenceOf(demandAlternative[<d,a>])*(a.fixedProcessingCost
//	+a.variableProcessingCost*d.quantity);

dexpr float TotalProcessingCost = 
	sum(<d,a> in DemandAlternatives) presenceOf(demandAlternative[<d,a>])*a.fixedProcessingCost
	+sum(<d,a> in DemandAlternatives) presenceOf(demandAlternative[<d,a>])*a.variableProcessingCost*d.quantity;

dexpr float TotalNonDeliveryCost = 
	sum(d in Demands) (1-presenceOf(demand[d]))*d.nonDeliveryVariableCost*d.quantity;
	
pwlFunction tardiness[d in Demands] = 
	piecewise{0->d.dueTime;d.tardinessVariableCost}(d.dueTime,0);	
	          				
dexpr float TardinessCost[d in Demands] =
	presenceOf(demand[d])*
	endEval(demand[d], tardiness[d]);
	 
dexpr float TotalTardinessCost = 
	sum(d in Demands) TardinessCost[d]; 

//Used by post-processing
dexpr int SetupCost[<d,a> in DemandAlternatives][r in Resources] = 
	setupCostArray[r]
         [resourceTypeOfPrev[<d,a>]]
		 [d.productId]; 

dexpr int TotalSetupCost = 
	sum(<d,a> in DemandAlternatives, r in Resources: a.resourceId == r.resourceId) 
	setupCostArray[r]
         [resourceTypeOfPrev[<d,a>]]
		 [d.productId]; 

dexpr float WeightedNonDeliveryCost= item(CriterionWeights, ord(CriterionWeights, <"NonDeliveryCost">)).weight*TotalNonDeliveryCost;
dexpr float WeightedProcessingCost=item(CriterionWeights, ord(CriterionWeights, <"ProcessingCost">)).weight*TotalProcessingCost;
dexpr float WeightedSetupCost=item(CriterionWeights, ord(CriterionWeights, <"SetupCost">)).weight*TotalSetupCost;
dexpr float WeightedTardinessCost=item(CriterionWeights, ord(CriterionWeights, <"TardinessCost">)).weight*TotalTardinessCost;
dexpr float TotalWeightedCost = WeightedNonDeliveryCost+WeightedProcessingCost+WeightedSetupCost+WeightedTardinessCost;


//Environment settings
execute {
  cp.param.Workers = 1
  cp.param.TimeLimit = Opl.card(Demands); 
  
  //cp.param.DefaultInferenceLevel = "Low"; 
  //cp.param.DefaultInferenceLevel = "Basic"; 
  //cp.param.DefaultInferenceLevel = "Medium"; 
  //cp.param.DefaultInferenceLevel = "Extended";
  //cp.param.SearchType = "Restart";
  //cp.param.SearchType = "DepthFirst";
  //cp.param.SearchType = "MultiPoint";
}

//Objective
minimize 
	TotalWeightedCost;
	
//Constraints
subject to {
	
	//All steps for a demand should be present when the demand itself is present
	forall(d in Demands, s in Steps : d.productId == s.productId) {
		(presenceOf(demand[d]) == presenceOf(demandStep[<d,s>]));
	}
	
	//A demand cannot be finished before its deliverymin time
	forall(d in Demands) {
		endOf(demand[d]) >= d.deliveryMin;	
	}
	
	//No overlap between steps on a single resource
	forall(r in Resources)
	  noOverlap(resources[r], ResourceTransitionTimes[r], 1);
	
	//Steps of a demand must be within the demand interval
	forall(d in Demands)
    	span(demand[d], all(<d,s> in DemandSteps) demandStep[<d,s>]);
    	
    //Redundant constraint 1 
    forall(ordered ds1,ds2 in DemandSteps : ds1.demand.demandId == ds2.demand.demandId) {
    	startOf(demandStep[ds2]) >= endOf(demandStep[ds1]);
    }
	
	//Demand step precedences
	forall(<d,s1> in DemandSteps, <d,s2> in DemandSteps) {
		forall(p in Precedences : (p.predecessorId == s1.stepId) && (p.successorId == s2.stepId)&&(p.delayMin<p.delayMax)) {
			endBeforeStart(demandStep[<d,s1>], demandStep[<d,s2>], maxl(p.delayMin,0));
			
			//Maximal delay between steps
			//startOf(demandStep[<d,s2>])-endOf(demandStep[<d,s1>]) <= p.delayMax;
			startBeforeEnd(demandStep[<d,s2>],demandStep[<d,s1>],-p.delayMax);
 		}			
	}
	
	//A demand cannot be scheduled if delayMin is higher than delayMax 
	forall(<d,s> in DemandSteps, pr in Precedences : 
			pr.delayMin > pr.delayMax && 
			(pr.predecessorId == s.stepId || pr.successorId == s.stepId)) {
		!presenceOf(demand[d]);
	}
	
	//Alternatives for a step
	forall(<d,s> in DemandSteps) {
		alternative(demandStep[<d,s>], all(<d,alt> in DemandAlternatives: alt.stepId==s.stepId) demandAlternative[<d,alt>]);
	}
		
	//Setuptime for step alternatives
	forall(<da, r> in DemandAlternativeResources, s in Steps, su in Setups : 
			da.a.stepId == s.stepId && s.setupResourceId != "NULL" && su.setupMatrixId == r.setupMatrixId) {
		//a setup must be scheduled iff the subsequent stepalternative is scheduled
		presenceOf(demandAlternative[da]) == presenceOf(setups[da]);
		startAtEnd(demandAlternative[da], setups[da]);
		lengthOf(setups[da]) == setupTimeArray[r]
											  [typeOfPrev(resources[r], demandAlternative[da], r.initialProductId, -1)]
											  [s.productId];
	}
	
	//A demandstep should use a single suitable storage tank
	forall(<d, ps> in DemandSteps) {
		alternative(storageSteps[<d, ps>], all(sp in StorageProductions : sp.prodStepId == ps.stepId) storageAltSteps[<d, sp>]);
	}
	
	//Storage must be present when there is any time interval between two consecutive demand steps
	forall(<d, ps1> in DemandSteps, <d, ps2> in DemandSteps, <d, sp> in DemandStorages : 
		sp.prodStepId == ps1.stepId && sp.consStepId == ps2.stepId) {
			(startOf(demandStep[<d,ps2>])-endOf(demandStep[<d,ps1>]) > 0) => presenceOf(storageSteps[<d, ps1>]);		
	}
	
//	forall(<d, s1> in DemandSteps, <d, s2> in DemandSteps, pr in Precedences, <d, sp> in DemandStorages : 
//			s1.stepId == sp.prodStepId && s2.stepId == sp.consStepId &&
//			pr.predecessorId == sp.prodStepId && pr.successorId == sp.consStepId) {
//
//		endAtStart(demandStep[<d, s1>], storageAltSteps[<d, sp>]) &&
//		startAtEnd(demandStep[<d, s2>], storageAltSteps[<d, sp>]);
//	}
	
	forall(<d, s1> in DemandSteps, <d, s2> in DemandSteps, pr in Precedences, <d, sp> in DemandStorages : 
		s1.stepId == sp.prodStepId && s2.stepId == sp.consStepId &&
		pr.predecessorId == sp.prodStepId && pr.successorId == sp.consStepId) {
			endAtStart(demandStep[<d, s1>], storageAltSteps[<d, sp>]) &&
			startAtEnd(demandStep[<d, s2>], storageAltSteps[<d, sp>]);
	}
	
	//A storaretank cannot exceed maximum capacity
	forall(r in StorageTanks) {
		storageTankUsage[r] <= r.quantityMax;
	}
	
	//Storage tank can only hold one type of product simultaneously
	forall(r in StorageTanks)
		forall(<d, sp> in DemandStorages : sp.storageTankId == r.storageTankId)
			alwaysEqual(tankState[r], storageAltSteps[<d, sp>], d.productId);
	
	//Old (incorrect) constraint: setuptime was part of the storageStep
	//Setuptime for storage tanks
	//forall(<<d, sp>, p1, p2> in DemandStorageProducts, r in StorageTanks, su in Setups : 
	//		sp.storageTankId == r.storageTankId && su.fromState == p1.productId && su.toState == p2.productId) {
	//	!presenceOf(storageAltSteps[<d, sp>]) || (
	//		lengthOf(storageAltSteps[<d, sp>]) >= su.setupTime
	//	);
	//}
	
	//symmetry constraint
	/*forall(<d, s> in DemandSteps,<d, sp> in DemandStorages : s.stepId==sp.prodStepId) {
		startBeforeStart(demandStep[<d,s>],storageAltSteps[<d, sp>]); 
	}*/
}

//Post Processing
tuple DemandAssignment {
  key string demandId; 
  int startTime;    	
  int endTime;
  float nonDeliveryCost;
  float tardinessCost;
};

{DemandAssignment} demandAssignments = {
	<d.demandId, 
	  startOf(demand[d]), 
	  endOf(demand[d]), 
	  d.nonDeliveryVariableCost*d.quantity * (1-presenceOf(demand[d])),
	  endEval(demand[d], tardiness[d])> 
	 | d in Demands
};

tuple StepAssignment {
  	key string demandId; 
  	key string stepId;  	
  	int startTime;    	
  	int endTime;
  	string resourceId;
	float procCost;
  	float setupCost;
  	int endTimeSetup;
  	int startTimeSetup;
	string setupResourceId;
};



{StepAssignment} stepAssignments = {
	<d.demandId,
	a.stepId,
	startOf(demandAlternative[<d,a>]),
	endOf(demandAlternative[<d,a>]),
	a.resourceId,
//<<<<<<< HEAD
		 a.fixedProcessingCost
	+ a.variableProcessingCost*d.quantity,
//=======
//	a.fixedProcessingCost + ftoi(round(d.quantity*a.variableProcessingCost)),
//>>>>>>> 378baf2579184433c759fef35c066424b1abb4cd
	SetupCost[<d,a>][r],
	endOf(setups[<d,a>]),
	startOf(setups[<d,a>]),
	s.setupResourceId> 
	
	| <d,a> in DemandAlternatives, r in Resources, s in Steps, su in Setups : presenceOf(demandAlternative[<d,a>]) &&
				a.resourceId == r.resourceId && a.stepId == s.stepId
	//|<d,a> in DemandAlternatives,s in Steps//, r in Resources,set in Setups
	//:presenceOf(demandAlternative[<d,a>])==true&&s.productId == d.productId && a.stepId == s.stepId
	//&&a.resourceId==r.resourceId&&r.setupMatrixId==set.setupMatrixId&& d.productId==set.toState
};

tuple StorageAssignment {
  key string demandId; 
  key string prodStepId;  	
  int startTime;    	
  int endTime;
  int quantity;
  string storageTankId;
};

{StorageAssignment} storageAssignments = {
	<d.demandId,
	sp.prodStepId,
	startOf(storageAltSteps[<d,sp>]),
	endOf(storageAltSteps[<d,sp>]),
	d.quantity,
	sp.storageTankId>
	| 
	<d,sp> in DemandStorages : presenceOf(storageAltSteps[<d,sp>])==true
};

//Output
execute {
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
    writeln("Total Weighted Cost        : ", TotalWeightedCost);
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
}
