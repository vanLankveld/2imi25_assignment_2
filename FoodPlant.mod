//Student names and numbers:
//Guus van Lankveld		0629468		g.v.lankveld@student.tue.nl
//Xiayang Hao			0892474		x.hao@student.tue.nl

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
	in d.deliveryMin..d.deliveryMax
	size(0..(d.deliveryMax-d.deliveryMin));

tuple DemandStep {
	Demand demand;
	Step step;
}

{DemandStep} DemandSteps = {<d, s> | d in Demands, s in Steps : d.productId == s.productId};

//Each demand and each step for a demand which is scheduled. Since not every demand needs to be scheduled, the interval is optional
dvar interval demandStep[<d,s> in DemandSteps]
	optional
	in lowestDeliveryMin..highestDeliveryMax
	size(
		min(a in Alternatives : a.stepId == s.stepId) (a.fixedProcessingTime + ftoi(round(d.quantity*a.variableProcessingTime)))
		..
		((max(sr in Setups : sr.toState == s.productId) sr.setupTime) + 
			max(a in Alternatives : a.stepId == s.stepId) (a.fixedProcessingTime + ftoi(round(d.quantity*a.variableProcessingTime))))
	);

//Alternatives for each step scheduled in 
tuple DemandAlternative{
	Demand d;
	Alternative a;
}

{DemandAlternative} DemandAlternatives ={<d,a>|d in Demands, s in Steps, a in Alternatives : 
			s.productId == d.productId && a.stepId == s.stepId};		
			
dvar interval demandAlternative[<d,a> in DemandAlternatives]
	optional
	in lowestDeliveryMin..highestDeliveryMax
	size (
		(a.fixedProcessingTime+ftoi(round(a.variableProcessingTime*d.quantity)))
		..
		((max(sr in Setups, s in Steps : sr.toState == s.productId && s.stepId == a.stepId) sr.setupTime)+
			(a.fixedProcessingTime+ftoi(round(a.variableProcessingTime*d.quantity))))
	);
	
dvar sequence resources[r in Resources] 
	in all(d in Demands, s in Steps, a in Alternatives : 
			s.productId == d.productId && a.stepId == s.stepId && a.resourceId == r.resourceId) demandAlternative[<d,a>];
	
tuple DemandProduction {
	Demand d;
	Step ps;
}

{DemandProduction} DemandProductions = {<d, ps> | d in Demands, ps in Steps : d.productId == ps.productId};
	
dvar interval storageSteps[<d, ps> in DemandProductions]
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

tuple DemandStorageProduct {
	DemandStorage ds;
	Product fromProduct;
	Product toProduct;
}

{DemandStorageProduct} DemandStorageProducts = {
	<<d, sp>, p1, p2> | <d, sp> in DemandStorages, p1 in Products, p2 in Products, s1 in Steps, s2 in Steps : 
	sp.prodStepId == s1.stepId && sp.consStepId == s2.stepId && s1.productId == p1.productId && s2.productId == s2.productId
};

cumulFunction storageTanks[r in StorageTanks] =
(sum(<d,sp> in DemandStorages 
   : sp.storageTankId == r.storageTankId)
   pulse(storageAltSteps[<d,sp>], d.quantity));
		
//Expressions
dexpr int TotalFixedProcessingCost = 
	sum(<d,a> in DemandAlternatives) presenceOf(demandAlternative[<d,a>])*a.fixedProcessingCost;

dexpr float TotalVariableProcessingCost = 
	sum(<d,a> in DemandAlternatives) presenceOf(demandAlternative[<d,a>])*a.variableProcessingCost*d.quantity;

dexpr float TotalProcessingCost = TotalFixedProcessingCost+TotalVariableProcessingCost;

dexpr float TotalNonDeliveryCost = 
	sum(d in Demands) (1-presenceOf(demand[d]))*d.nonDeliveryVariableCost*d.quantity;
	

	
pwlFunction tardiness[d in Demands] = 
	piecewise{0->d.dueTime;d.tardinessVariableCost}(0,0);	
	          				
dexpr float TardinessCost[d in Demands] =
	endEval(demand[d], tardiness[d]);
	 
dexpr float TotalTardinessCost = 
	sum(d in Demands) TardinessCost[d]; 
	
dexpr float TotalSetupCost = 
	sum(<d, s> in DemandSteps, a in Alternatives, r in Resources, su in Setups : 
			a.resourceId == r.resourceId && a.stepId == s.stepId && r.setupMatrixId == su.setupMatrixId &&
			su.fromState == r.initialProductId && su.toState == s.productId) 
			presenceOf(demandStep[<d,s>]) * su.setupCost;
dexpr float WeightedNonDeliveryCost= max(c in CriterionWeights :c.criterionId == "NonDeliveryCost")(c.weight*TotalNonDeliveryCost);
dexpr float WeightedProcessingCost=max(c in CriterionWeights :c.criterionId =="ProcessingCost")(c.weight*TotalProcessingCost);
dexpr float WeightedSetupCost=max(c in CriterionWeights :c.criterionId =="SetupCost")(c.weight*TotalSetupCost);
dexpr float WeightedTardinessCost=max(c in CriterionWeights :c.criterionId =="TardinessCost")(c.weight*TotalTardinessCost);

//Environment settings
execute {
  cp.param.Workers = 1
  cp.param.TimeLimit = Opl.card(Demands); 
}

//Objective
minimize 
	WeightedNonDeliveryCost + 
	WeightedProcessingCost +
	WeightedSetupCost + 
	WeightedTardinessCost;
	
//Constraints
subject to {
	//All steps for a demand should be present when the demand itself is present
	forall(d in Demands, s in Steps : d.productId == s.productId) {
		//Old version. Not correct since this still allows demandStep[x][y] to be present  even if demand[x] is absent
		//(presenceOf(demand[d]) => presenceOf(demandStep[d][s]));
		
		(presenceOf(demand[d]) == presenceOf(demandStep[<d,s>]));
	}
	
	//No overlap between steps on a single resource
	forall(r in Resources)
	  noOverlap(resources[r]);
	
	//Steps of a demand must be within the demand interval
	forall(d in Demands)
    	span(demand[d], all(<d,s> in DemandSteps) demandStep[<d,s>]);
	
	//Demand step precedences
	forall(<d,s1> in DemandSteps, <d,s2> in DemandSteps) {
		forall(p in Precedences : (p.predecessorId == s1.stepId) && (p.successorId == s2.stepId)) {
			endBeforeStart(demandStep[<d,s1>], demandStep[<d,s2>], p.delayMin);
			
			//Maximal delay between steps
			startOf(demandStep[<d,s2>])-endOf(demandStep[<d,s1>]) <= p.delayMax;
 		}			
	}
	
	//Alternatives for a step
	forall(<d,s> in DemandSteps) {
		alternative(demandStep[<d,s>], all(<d,alt> in DemandAlternatives: alt.stepId==s.stepId) demandAlternative[<d,alt>]);
	}
	
	//Length of each alternative, including the setup time
	forall(<d,a> in DemandAlternatives, r in Resources, s in Steps, su in Setups : 
				a.resourceId == r.resourceId && a.stepId == s.stepId && r.setupMatrixId == su.setupMatrixId &&
				su.fromState == r.initialProductId && su.toState == s.productId) {
		//Alternative is either not present or has length of processingtime+setuptime
		!presenceOf(demandAlternative[<d,a>]) || (
			lengthOf(demandAlternative[<d,a>]) == (
				a.fixedProcessingTime + ftoi(round(d.quantity*a.variableProcessingTime)) + (
					((s.setupResourceId != "NULL") && (r.setupMatrixId != "NULL")) * (su.setupTime)
				)
			)
		);
	}
	
	//A demandstep should use a single suitable storage tank
	forall(<d, ps> in DemandProductions) {
		alternative(storageSteps[<d, ps>], all(sp in StorageProductions : sp.prodStepId == ps.stepId) storageAltSteps[<d, sp>]);
	}
	
	forall(<d, ps1> in DemandProductions, <d, ps2> in DemandProductions, <d, sp> in DemandStorages : 
			sp.prodStepId == ps1.stepId && sp.consStepId == ps2.stepId) {
		(startOf(demandStep[<d,ps2>])-endOf(demandStep[<d,ps1>]) > 0)	== presenceOf(storageSteps[<d, ps1>]);		
	}
	
	forall(<d, s1> in DemandSteps, <d, s2> in DemandSteps, pr in Precedences, <d, sp> in DemandStorages : 
			s1.stepId == sp.prodStepId && s2.stepId == sp.consStepId &&
			pr.predecessorId == sp.prodStepId && pr.successorId == sp.consStepId) {
		endAtStart(demandStep[<d, s1>], storageAltSteps[<d, sp>]) &&
		startAtEnd(demandStep[<d, s2>], storageAltSteps[<d, sp>]);
	}
	
	//A storaretank cannot exceed maximum capacity
	forall(r in StorageTanks) {
		storageTanks[r] <= r.quantityMax;
	}
	
	//Setuptime for storage tanks
	forall(<<d, sp>, p1, p2> in DemandStorageProducts, r in StorageTanks, su in Setups : 
			sp.storageTankId == r.storageTankId && su.fromState == p1.productId && su.toState == p2.productId) {
		!presenceOf(storageAltSteps[<d, sp>]) || (
			lengthOf(storageAltSteps[<d, sp>]) >= su.setupTime
		);
	}
}

//Post Processing
tuple DemandAssignment {
  key string demandId; 
  int startTime;    	
  int endTime;
  float nonDeliveryCost;
  float tardinessCost;
};

//{DemandAssignment} demandAssignments = fill in from your decision variables.
{DemandAssignment} demandAssignments = {
	<d.demandId, 
	  startOf(demand[d]), 
	  endOf(demand[d]), 
	  d.nonDeliveryVariableCost,
	  d.tardinessVariableCost> 
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
	a.fixedProcessingTime + ftoi(round(d.quantity*a.variableProcessingTime)),
	su.setupCost,
	startOf(demand[d]),
	 //endOf(demand[d1]),
	startOf(demand[d])+su.setupTime,
	s.setupResourceId> 
	
	|<d,a> in DemandAlternatives, r in Resources, s in Steps, su in Setups : presenceOf(demandAlternative[<d,a>])==true&&
				a.resourceId == r.resourceId && a.stepId == s.stepId && r.setupMatrixId == su.setupMatrixId &&
				su.fromState == r.initialProductId && su.toState == s.productId
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
// 		if (sa.setupCost > 0)
// 		  write(", setup cost: ", sa.setupCost);
// 		writeln();
// 		if (sa.startTimeSetup < sa.endTimeSetup)
// 			writeln("   setup step: [", 
// 			        sa.startTimeSetup, ",", sa.endTimeSetup, "] ",
// 			        "on ", sa.setupResourceId);   
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
