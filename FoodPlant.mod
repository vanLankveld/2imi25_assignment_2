//Student names and numbers:
//Guus van Lankveld		0629468		g.v.lankveld@student.tue.nl
//Xiayang Hao			0892474		x.hao@student.tue.nl

//The model as submitted is the one that gave the best result on "instance0".

/*REMOVE THIS BEFORE SUBMITTING TO TEACHER:

- Say something about setup costs for storage tank not being used
- Explain implications in report when they are used.
- Run mutipul time for a good solution
- (startOf(demandStep[<d,ps2>])-endOf(demandStep[<d,ps1>]) > 0) == presenceOf(storageSteps[<d, ps1>]); == VS =>

- Searchphases
	- instance0: Setting searchphases decreases performance

*/


using CP;

// ==================================== Input data ====================================
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


// ================================ Decision variables ================================

//Interval ecompassing a demand
dvar interval demand[d in Demands]
	optional
	in 0..d.deliveryMax
	size(0..d.deliveryMax);

//Tuple used to join a demand and its steps
tuple DemandStep {
	Demand demand;
	Step step;
}

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

//Tuple used to join demands and the possible alternatives for that demand
tuple DemandAlternative{
	Demand d;
	Alternative a;
}

{DemandAlternative} DemandAlternatives ={<d,a>|d in Demands, s in Steps, a in Alternatives : 
			s.productId == d.productId && a.stepId == s.stepId};		
			
//Alternatives which are scheduled for a demand
dvar interval demandAlternative[<d,a> in DemandAlternatives]
	optional
	in 0..d.deliveryMax
	size (
		a.fixedProcessingTime+ftoi(round(a.variableProcessingTime*d.quantity))
	);

//All product ID's in the data set
{int} ProductIds = {p.productId | p in Products};

//Non declarative approach
//int setupCostArray[Resources][ProductIds][ProductIds];
//execute {
//  for(var r in Resources) {
//    for(var s in Setups) {
//      setupCostArray[r][s.fromState][s.toState] = 
//        s.setupCost;
//    }				  
//  }
//} 

//Data cube containing all setup costs for each possible combinations of resources and 'from' and 'to' products
int setupCostArray[r in Resources][p1 in ProductIds union {- 1}][p2 in ProductIds] = 
	sum( <r.setupMatrixId, p1, p2, setupTime, setupCost > in Setups) setupCost;

//Data cube containing all setup times for each possible combinations of resources and 'from' and 'to' products
int setupTimeArray[r in Resources][p1 in ProductIds union {- 1}][p2 in ProductIds] = 
	sum( <r.setupMatrixId, p1, p2, setupTime, setupCost > in Setups) setupTime;

//Scheduled setup preceding a schedulted DemandAlternative
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

//All transition times on a resource between two given products
{TransitionTime} ResourceTransitionTimes[r in Resources] = {
	<fromProduct, toProduct, setupTime> | 
	<setupMatrixId, fromProduct, toProduct, setupTime, setupCost> in Setups : 
	r.setupMatrixId == setupMatrixId
};

//Joins a DemandAlternative and its Resource
tuple DemandAlternativeResource {
	DemandAlternative demandAlternative;
	Resource resource;
}

{DemandAlternativeResource} DemandAlternativeResources = {
	<<d,a>, r> | <d,a> in DemandAlternatives, r in Resources : a.resourceId == r.resourceId
};

//The intervals scheduled on a given Resource
dvar sequence resources[r in Resources] 
	in all(<<d,a>, r> in DemandAlternativeResources) demandAlternative[<d,a>] 
	types all(<<d,a>, r> in DemandAlternativeResources) d.productId;
	
{TransitionTime} StorageTransitionTimes[r in StorageTanks] = {
	<fromProduct, toProduct, setupTime> | 
	<setupMatrixId, fromProduct, toProduct, setupTime, setupCost> in Setups : 
	r.setupMatrixId == setupMatrixId
};

//Scheduled storage intervals for a given productionstep in a demand
dvar interval storageSteps[<d, ps> in DemandSteps]
	optional
	in 0..d.deliveryMax;

//Joins a demand and its StorageProduction items
tuple DemandStorage {
  Demand demand;
  StorageProduction storageProduction;
}

{DemandStorage} DemandStorages =
{<d,sp> | d in Demands, sp in StorageProductions, st in Steps 
       : sp.prodStepId == st.stepId && st.productId == d.productId};

//Storage alternatives scheduled for given DemandStorages
dvar interval storageAltSteps[<d,sp> in DemandStorages]
	optional
	in 0..d.deliveryMax;
		
		
// ================================ Expressions and Functions ================================

//Old expressions:
//dexpr int TotalFixedProcessingCost = 
//	sum(<d,a> in DemandAlternatives) presenceOf(demandAlternative[<d,a>])*a.fixedProcessingCost;
//
//dexpr float TotalVariableProcessingCost = 
//	sum(<d,a> in DemandAlternatives) presenceOf(demandAlternative[<d,a>])*a.variableProcessingCost*d.quantity;

//should be the same as the final implementation but gives worse result
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
	
//Gives the previous product type which has been processed on the resource associated with the given DemandAlternative
dexpr int resourceTypeOfPrev[<d,a> in DemandAlternatives] =
	typeOfPrev(
		resources[item(Resources, <a.resourceId>)], 
		demandAlternative[<d,a>], 
		item(Resources, <a.resourceId>).initialProductId,
		-1
	);

//Used in the post-processing phase, returns the setupcost of a single DemandAlternative, Resource combination
dexpr int SetupCost[<d,a> in DemandAlternatives][r in Resources] = 
	setupCostArray[r]
         [resourceTypeOfPrev[<d,a>]]
		 [d.productId]; 

dexpr int TotalSetupCost = 
	sum(<d,a> in DemandAlternatives, r in Resources: a.resourceId == r.resourceId) 
	setupCostArray[r]
         [resourceTypeOfPrev[<d,a>]]
		 [d.productId]; 

//Weighed costs
dexpr float WeightedNonDeliveryCost= item(CriterionWeights, ord(CriterionWeights, <"NonDeliveryCost">)).weight*TotalNonDeliveryCost;
dexpr float WeightedProcessingCost=item(CriterionWeights, ord(CriterionWeights, <"ProcessingCost">)).weight*TotalProcessingCost;
dexpr float WeightedSetupCost=item(CriterionWeights, ord(CriterionWeights, <"SetupCost">)).weight*TotalSetupCost;
dexpr float WeightedTardinessCost=item(CriterionWeights, ord(CriterionWeights, <"TardinessCost">)).weight*TotalTardinessCost;
dexpr float TotalWeightedCost = WeightedNonDeliveryCost+WeightedProcessingCost+WeightedSetupCost+WeightedTardinessCost;

//State function used to ensure that a storagetank can only contain one type of product at a given time.
statefunction tankState[r in StorageTanks] with StorageTransitionTimes[r];

//Cumulfunction used to calculate the accumulated contents of a tank at a given time
cumulFunction storageTankUsage[r in StorageTanks] =
(sum(<d,sp> in DemandStorages 
   : sp.storageTankId == r.storageTankId)
   pulse(storageAltSteps[<d,sp>], d.quantity));
   

// ================================ Environment settings ================================
execute {
  cp.param.Workers = 1
  cp.param.TimeLimit = Opl.card(Demands); 
  
  //Some different parameters used for testing.
  //cp.param.DefaultInferenceLevel = "Low"; 
  //cp.param.DefaultInferenceLevel = "Basic"; 
  //cp.param.DefaultInferenceLevel = "Medium"; 
  //cp.param.DefaultInferenceLevel = "Extended";
  //cp.param.SearchType = "Restart";
  //cp.param.SearchType = "DepthFirst";
  //cp.param.SearchType = "MultiPoint";

  //cp.param.searchType = "DepthFirst";
  //cp.param.searchType = "Restart";
  //cp.param.searchType = "MultiPoint";
  //cp.param.searchType = "Auto";
  
  //cp.param.restartfaillimit = 50;
  //cp.param.restartfaillimit = 100;
  //cp.param.restartfaillimit = 200;
  
  //Search phases, see the report for the other combinations which were used to test
  /*
  cp.setSearchPhases(
   	f.searchPhase(resources),
   	f.searchPhase(demandAlternative),
   	f.searchPhase(storageAltSteps)
  );
  */
}

//Objective
minimize 
	TotalWeightedCost;
	
// ================================ Constraints ================================

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
		alternative(demandStep[<d,s>], all(<d,alt> in DemandAlternatives : alt.stepId==s.stepId) 
			demandAlternative[<d,alt>]);
	}
		
	//Setuptime for step alternatives
	forall(<da, r> in DemandAlternativeResources, s in Steps, su in Setups : 
			da.a.stepId == s.stepId && s.setupResourceId != "NULL" && su.setupMatrixId == r.setupMatrixId) {
		//a setup must be scheduled iff the subsequent stepalternative is scheduled
		presenceOf(demandAlternative[da]) == presenceOf(setups[da]);
		//endBeforeStart(setups[da], demandAlternative[da]); //Poor performance on instance0
		startAtEnd(demandAlternative[da], setups[da]);
		lengthOf(setups[da]) == setupTimeArray[r]
											  [typeOfPrev(resources[r], demandAlternative[da], r.initialProductId, -1)]
											  [s.productId];
	}
	
	//A demandstep should use a single suitable storage tank
	forall(<d, ps> in DemandSteps) {
		alternative(storageSteps[<d, ps>], all(sp in StorageProductions : sp.prodStepId == ps.stepId) storageAltSteps[<d, sp>]);
	}
	
	//Redundant constraint: If a demand is not delivered, no storage should be used for that demand
	/*forall(<d, ps> in DemandSteps) {
		!presenceOf(demand[d]) => !presenceOf(storageSteps[<d, ps>]);	
	}*/
	
	//Redundant constraint: If there is a minimum delay greater than zero between two production steps, 
	//storage should be used between those two steps
	/*forall(<d,s1> in DemandSteps, <d,s2> in DemandSteps, 
		<s1.stepId, s2.stepId, delayMin, delayMax> in Precedences : delayMin > 0) {
			presenceOf(storageSteps[<d, s1>]);
	}*/
	
	//Storage must be present when there is any time interval between two consecutive demand steps
	forall(<d, ps1> in DemandSteps, <d, ps2> in DemandSteps, 
			<d, <ps1.stepId, stid, ps2.stepId>> in DemandStorages) {
			//worse performance but correct result on STI foodSetup2
			//(startOf(demandStep[<d,ps2>])-endOf(demandStep[<d,ps1>]) > 0) => presenceOf(storageSteps[<d, ps1>]);				
			(startOf(demandStep[<d,ps2>])-endOf(demandStep[<d,ps1>]) > 0) == presenceOf(storageSteps[<d, ps1>]);		
	}


// Old, slower method	
//	forall(<d, s1> in DemandSteps, <d, s2> in DemandSteps, pr in Precedences, <d, sp> in DemandStorages : 
//			s1.stepId == sp.prodStepId && s2.stepId == sp.consStepId &&
//			pr.predecessorId == sp.prodStepId && pr.successorId == sp.consStepId) {
//
//		endAtStart(demandStep[<d, s1>], storageAltSteps[<d, sp>]) &&
//		startAtEnd(demandStep[<d, s2>], storageAltSteps[<d, sp>]);
//	}
	
	//A storage step should start extactly when the previous production step ends and end extactly when
	//the next step starts
	forall(<d, s1> in DemandSteps, <d, s2> in DemandSteps, 
		<s1.stepId, s2.stepId, dmin, dmax> in Precedences, 
		<d, <s1.stepId, storageTankId, s2.stepId>> in DemandStorages) {
			endAtStart(demandStep[<d, s1>], storageAltSteps[<d, <s1.stepId, storageTankId, s2.stepId>>]) &&
			startAtEnd(demandStep[<d, s2>], storageAltSteps[<d, <s1.stepId, storageTankId, s2.stepId>>]);
	}
	
	//A storaretank cannot exceed maximum capacity
	forall(r in StorageTanks) {
		storageTankUsage[r] <= r.quantityMax;
	}
	
	//Storage tank can only hold one type of product simultaneously
	forall(r in StorageTanks)
		forall(<d, sp> in DemandStorages : sp.storageTankId == r.storageTankId)
			alwaysEqual(tankState[r], storageAltSteps[<d, sp>], d.productId);
}

//================================ Post Processing ================================
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
	a.fixedProcessingCost
	+ a.variableProcessingCost*d.quantity,
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

//================================ Output ================================
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
