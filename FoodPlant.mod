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

int maxQuantity = max(d in Demands) d.quantity;
int lowestDeliveryMin = min(d in Demands) d.deliveryMin;
int highestDeliveryMax = max(d in Demands) d.deliveryMax;

{Step} stepsForProduct[p in Products] = {s | s in Steps : s.productId == p.productId};

//Decision variables
dvar interval productionStep[d in Demands][i in 1..maxQuantity][j in 1..card(Steps)]
	optional
	in lowestDeliveryMin..highestDeliveryMax;

dvar sequence s in productionStep;

//Objective


//Environment settings
execute {
  cp.param.Workers = 1;
  cp.param.TimeLimit = Opl.card(Demands); 
}


//Constraints
subject to {
	
}

//Post Processing


//Output
execute {
  	writeln("Total Non-Delivery Cost    : ", TotalNonDeliveryCost);
  	writeln("Total Processing Cost      : ", TotalProcessingCost);
  	writeln("Total Setup Cost           : ", TotalSetupCost);
  	writeln("Total Tardiness Cost       : ", TotalTardinessCost);
  	writeln();
  	writeln("Weighted Non-Delivery Cost : ",WeightedNonDeliveryCost);
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
} 
