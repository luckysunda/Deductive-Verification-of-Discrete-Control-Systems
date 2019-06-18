var req1:bool;
var req2:bool;
var req3:bool;
var ack1:bool;
var ack2:bool;
var ack3: bool;
var oldack1:bool;
var oldack2:bool;
var oldack3:bool;
var oldreq1:bool;
var oldreq2:bool;
var oldreq3: bool;
var bit1:bool;
var bit2:bool;
var bit3:bool;
var oldbit1:bool;
var oldbit2:bool;
var oldbit3:bool;

function {:existential true}{:inline} Invariant(req1:bool,req2:bool,req3:bool,ack1:bool,ack2:bool,ack3:bool):bool;

procedure arbiter_inti()
ensures(oldack1 && ( req2 || req3))==> !ack1;
ensures(oldack2 && ( req1 || req3))==> !ack2;
ensures(oldack3 && ( req2 || req1))==> !ack3;
ensures Invariant(req1,req2,req3,ack1,ack2,ack3);


modifies bit1,bit2,bit3,oldreq1,oldreq2,oldreq3,oldbit1,oldbit2,oldbit3,ack1,ack2,ack3,oldack1,oldack2,oldack3,req1,req2,req3,bit1,bit2,bit3,oldbit1,oldbit2,oldbit3;
{
  
  havoc req1,req2,req3;
  bit1:=false;bit2:=false;bit3:=false;
 
  
  if(req1)
  { 
    if(bit1)
    {
      if(req3 || req2)
      {
        ack1:=false;
      }
    }
    else
    {
      ack1:=true;
    }
    
  }
  else
  {
    ack1:=false;
  }
  
  if(req2)
  { 
    if(bit2)
    {
      if(req3||req1)
      {
        ack2:=false;
      }
      else
      {
        if(!ack1 && !req3)
        {
          ack2:=true;
        }
        else{
          ack2:=false;
        }
      }
    }
    else
    {
      if(!ack1)
      {
        ack2:=true;
      }
      else
      {
	ack2:=false;
      }
      
    }
    
  }
  else
  {
    ack2:=false;
  }
 
  if(req3)
  { 
   if(ack1 || ack2)
   {
     ack3:=false;
   }
   else
   {
     ack3:=true;
   }
    
  }
  else
  {
    ack3:=false;
  }
  oldack1:=ack1;
  oldack2:=ack2;
  oldack3:=ack3;
  oldreq1:=req1;
  oldreq2:=req2;
  oldreq3:=req3;
  oldbit1:=bit1;
  oldbit2:=bit2;
  oldbit3:=bit3;
  bit1:=oldack1;
  bit2:=oldack2;
  bit3:=oldack3;
  havoc req1,req2,req3;
  
  
  if(req1)
  { 
    if(bit1)
    {
      if(req3 || req2)
      {
        ack1:=false;
      }
    }
    else
    {
      ack1:=true;
    }
    
  }
  else
  {
    ack1:=false;
  }
  
  if(req2)
  { 
    if(bit2)
    {
      if(req3||req1)
      {
        ack2:=false;
      }
      else
      {
        if(!ack1 && !req3)
        {
          ack2:=true;
        }
        else{
          ack2:=false;
        }
      }
    }
    else
    {
      if(!ack1)
      {
        ack2:=true;
      }
      else
      {
	ack2:=false;
      }
      
    }
    
  }
  else
  {
    ack2:=false;
  }
 
  if(req3)
  { 
   if(ack1 || ack2)
   {
     ack3:=false;
   }
   else
   {
     ack3:=true;
   }
    
  }
  else
  {
    ack3:=false;
  }
}


procedure arbiter_induction()

requires(oldack1 && ( req2 || req3))==> !ack1;
ensures(oldack1 && ( req2 || req3))==> !ack1;

requires(oldack2 && ( req1 || req3))==> !ack2;
requires(oldack3 && ( req2 || req1))==> !ack3;
ensures(oldack2 && ( req1 || req3))==> !ack2;
ensures(oldack3 && ( req2 || req1))==> !ack3;


requires Invariant(req1,req2,req3,ack1,ack2,ack3);
ensures Invariant(req1,req2,req3,ack1,ack2,ack3);
modifies bit1,bit2,bit3,oldbit1,oldbit2,oldbit3,req1,req2,req3,ack1,ack2,ack3, oldack1,oldack2,oldack3,oldreq1,oldreq2,oldreq3;
{
  
  oldreq1:=req1;
  oldreq2:=req2;
  oldreq3:=req3;
  oldack1:=ack1;
  oldack2:=ack2;
  oldack3:=ack3;
  oldbit1:=bit1;
  oldbit2:=bit2;
  oldbit3:=bit3;
 
  bit1:=oldack1;
  bit2:=oldack2;
  bit3:=oldack3;
  
  havoc req1,req2,req3;
  
  if(req1)
  { 
    if(bit1)
    {
      if(req3 || req2)
      {
        ack1:=false;
      }
    }
    else
    {
      ack1:=true;
    }
    
  }
  else
  {
    ack1:=false;
  }
  
  if(req2)
  { 
    if(bit2)
    {
      if(req3||req1)
      {
        ack2:=false;
      }
      else
      {
        if(!ack1 && !req3)
        {
          ack2:=true;
        }
        else{
          ack2:=false;
        }
      }
    }
    else
    {
      if(!ack1)
      {
        ack2:=true;
      }
      else
      {
	ack2:=false;
      }
      
    }
    
  }
  else
  {
    ack2:=false;
  }
 
  if(req3)
  { 
   if(ack1 || ack2)
   {
     ack3:=false;
   }
   else
   {
     ack3:=true;
   }
    
  }
  else
  {
    ack3:=false;
  }  
}


