  var y1:int;
  var y2:int;
  var oy1:int;
  var oy2:int;
  var STATE:int;
  var OLDSTATE:int;
  var counter_:int;
  var oldcounter_:int;
  var sens_:bool;
  var oldsens_:bool;
  

  
function {:existential true} {:inline} Invariant (y1:int,y2:int,oy1:int,oy2:int,STATE:int,OLDSTATE:int,counter_:int,oldcounter_:int,,sens_:bool,oldsens_:bool):bool; 

procedure trafficlightinit()
ensures ((STATE==10 && STATE==20)==> y2==1);
ensures Invariant(y1,y2,oy1,oy2,STATE,OLDSTATE,counter_,oldcounter_,sens_,oldsens_);
modifies y1,y2,oy1,oy2;
modifies STATE, OLDSTATE;
modifies counter_,oldcounter_;
modifies sens_, oldsens_;
{
  
       
 
        STATE:=10; //init
        counter_:=0;
        havoc sens_;
          //compute ouptut
        if(STATE==20)
{
                        y1:=0;
                        y2:=2;
                }
                else if(STATE==30)
                {
                        y1:=1;
                        y2:=0;
                }
                else if(STATE==40)
                {
                        y1:=2;
                        y2:=0;
                }
                else if(STATE==50)
                {
                        y1:=0;
                        y2:=1;
                }


                else if(STATE==10)
                {
                         y1:=0;
                         y2:=1;
                } 
                else {
                          y1:=0;
                          y2:=0;
                      }
  // store previous output
oldsens_:=sens_;
oy1:=y1;
oy2:=y2;
oldcounter_:=counter_;
OLDSTATE:=STATE;
  //update state
  
  
if (counter_ < 31) 
{
       	counter_:= counter_+1;
}
if(STATE==40)
{
         if (counter_>= 10) 
         	{
                STATE :=50;
counter_ := 0;
}
}
else if(STATE==50)
{
        if (counter_ >= 3) 
        {
                 STATE := 10;
counter_ := 0;
}
}
else if(STATE==10)
{
if (counter_ >= 20)
{
       	STATE :=20;
}

}
else if(STATE==20)
{
        if (sens_) 
        {
                STATE := 30;
                counter_ := 0;
}
}
else if(STATE==30)
{
        if (counter_ >= 3) 
        {
                STATE := 40;
counter_ := 0;
}
        
} 

else
{
  STATE:=10;
counter_:=0;
}


}
procedure trafficupdate()
/*
requires(STATE==30 ==>(y1==0 && y2==2));
requires(STATE==10 ==>(y1==0 && y2==1));
requires(STATE==40 ==>(y1== 1&& y2==0));
requires(STATE==20 ==>(y1==0 && y2==1));
requires(STATE==50 ==>(y1==2 && y2==0));
*/

requires (oy1 == 1 ==> (y1 == 1 || y1 == 2));
ensures (oy1 == 1 ==> (y1 == 1 || y1 == 2));


modifies y1,y2;
modifies counter_, oldcounter_;
modifies STATE, OLDSTATE;
modifies oy1,oy2;
modifies sens_,oldsens_;

requires Invariant(y1,y2,oy1,oy2,STATE,OLDSTATE,counter_,oldcounter_,sens_,oldsens_);
ensures Invariant(y1,y2,oy1,oy2,STATE,OLDSTATE,counter_,oldcounter_,sens_,oldsens_);
{
  

  assume(counter_>=1 && counter_<35);
  
      // store previous output
                oldsens_:=sens_;
                oy1:=y1;
                oy2:=y2;
                OLDSTATE:=STATE;
                oldcounter_:=counter_;
     //update state
     
     
     if (counter_ < 31) {
                counter_:= counter_+1;
        }
        
        //read input
havoc sens_;
 //oldsens_:=sens_;
        if(STATE==40){
                 if (counter_>=10) {
                   counter_ := 0;
                        STATE :=50;

}
        }
        else if(STATE==50){
                if (counter_ >= 3) {
                  counter_ := 0;
                         STATE := 10;

}
        }
        else if(STATE==10){
                if (counter_ >= 20) {
                 
                        STATE :=20;


}
}
else if(STATE==20){
        if (sens_) {
          counter_ := 0;
                STATE := 30;

}
}
else if(STATE==30){
        if (counter_ >= 3) {
          counter_ := 0;
                STATE := 40;

}
        
}

            if(STATE==20){
                y1:=0;
                y2:=1;}
        
        else if(STATE==40){
                y1:=1;
                y2:=0;
        }
        else if(STATE==50)
        {
                y1:=2;
                y2:=0;
        }
        else if(STATE==30){
                y1:=0;
                y2:=2;
        }
        else if(STATE==10) 
        {
          y2:=1;
          y1:=0;
        }

         

 

}
