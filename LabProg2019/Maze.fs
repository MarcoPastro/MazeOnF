(*
* LabProg2019 - Progetto di Programmazione a.a. 2019-20
* Maze.fs: maze
* (C) 2019 Castellani Mattia & Pastrello Marco @ Universita' Ca' Foscari di Venezia
*)

module LabProg2019.Maze

open System
open External
open Gfx
open System.Text
open Engine

let mutable W=49
let mutable H=49

type CharInfo with
    static member wall = pixel.create (Config.wall_pixel_char, Color.White)
    static member menu = pixel.create (Config.menu_pixel_char,Color.Red)
    static member internal path = pixel.filled Color.Black
    static member internal solution = pixel.filled Color.Blue
    static member internal finish = pixel.filled Color.Red
    member this.isWall = this = pixel.wall

//the array that will become the maze
let maze= Array.create (W*H) (0,0,true)
//the variable that corresponds to the end of the maze
let mutable fine=((W-2),(H-2),false)

//the function that build the starting maze with only walls
let build() =
    let mutable counter=0
    for i=0 to (H-1) do
        for j=0 to (W-1) do
            maze.[counter]<-(j,i,true)
            counter<-counter+1

//the function that change a wall into a path of a cell that is passed 
let change c =
    let (x,y,w)=c
    maze.[y*W+x]<-(x,y,false)

//the function that returns a specific cell thanks to the positions passed
let cell a b =
    let mutable result=(-1,-1,true)
    for i in maze do 
        let (e,f,g) = i 
        in if (a=e && f=b) then result<-i
    result

//the function that returns true if the cell is a wall, or false if the cell is a path, thanks to the positions passed
let isWall a b = let (e,f,g)= (cell a b) 
                 in g                
                
//the function that returns true if the cell exists in the maze, or false if the cell doesn't exist in the maze, thanks to the positions passed
let isPresent a b =
    let mutable result=false
    for i in maze do 
        let (e,f,g) = i 
        in if (a=e && f=b) then result<-true
    result

//the function that returns true if it's possible to go left of a specific cell that is passed, or false if it isn't allow
let left c = let (a,b,wall) = c
             in if ((isPresent (a-2) b)&&(isPresent (a-1) b))
                then if ((isWall (a-2) b)&&(isWall (a-1) b)&&(isWall (a-1) (b-1))&&(isWall (a-1) (b+1)))
                     then true 
                     else false
                else false
//the function that returns true if it's possible to go up of a specific cell that is passed, or false if it isn't allow
let up c = let (a,b,wall) = c
           in if ((isPresent a (b-2)&&(isPresent a (b-1))))
              then if ((isWall a (b-2))&&(isWall a (b-1))&&(isWall (a+1) (b-1))&&(isWall (a-1) (b-1)))
                   then true 
                   else false
              else false
//the function that returns true if it's possible to go right of a specific cell that is passed, or false if it isn't allow
let right c = let (a,b,wall) = c
              in if ((isPresent (a+2) b)&&(isPresent (a+1) b))
                 then if ((isWall (a+2) b)&&(isWall (a+1) b)&&(isWall (a+1) (b+1))&&(isWall (a+1) (b-1)))
                      then true
                      else false
                 else false
//the function that returns true if it's possible to go down of a specific cell that is passed, or false if it isn't allow
let down c = let (a,b,wall) = c
             in if (isPresent a (b+2)&&(isPresent a (b+1)))
                then if ((isWall a (b+2))&&(isWall a (b+1))&&(isWall (a-1) (b+1))&&(isWall (a+1) (b+1)))
                     then true
                     else false
                else false
//the function that build all the paths of the maze
let path() =
    let mutable n=false
    let mutable k=0
    let mutable (a,b,wall) = cell 1 1
    
    in wall<- false 
    let rec aux visited =
        match visited with
        |[]->ignore()
        |t::ts->let (x,y,w2) = t
                change t
                let (xf,yf,wf)=fine
                let mutable neighbours=[]
                let mutable direction=""
                if(down t) then neighbours<-"d"::neighbours
                if(up t) then neighbours<-"u"::neighbours 
                if(left t) then neighbours<-"l"::neighbours 
                if(right t) then neighbours<-"r"::neighbours
                if(neighbours.Length<>0)
                then  match (rnd_int 0 (neighbours.Length-1)) with
                        |0->direction<-neighbours.[0]
                    
                        |1->direction<-neighbours.[1]

                        |2->direction<-neighbours.[2]


                        |3->direction<-neighbours.[3]

                        |_->direction<-""


                match direction with
                    |"d"->change (cell x (y+1))
                          aux ((cell x (y+1))::(x,y,w2)::ts)
                    |"u"->change (cell x (y-1))
                          aux((cell x (y-1))::(x,y,w2)::ts)
                    |"l"->change (cell (x-1) y)
                          aux((cell (x-1) y)::(x,y,w2)::ts)
                    |"r"->change (cell (x+1) y)
                          aux ((cell (x+1) y)::(x,y,w2)::ts)
                    |_->aux ts

    in aux ((a,b,wall)::[])
//the function that ensures that the end is reachable
let rec go_ahead x y=
    if(((isWall x (y-1))=false) || (((isWall (x-1) y))=false))
    then change (cell x y)
    else match (rnd_int 0 1) with
         |0->change (cell x (y-1))
             go_ahead x (y-1)
         |_->change (cell (x-1) y)
             go_ahead (x-1) y
//the function that create the end of the path in a static position
let staticEnd()=
    go_ahead (W-2) (H-2)
    if (isWall (W-2) (H-2))
    then change (cell (W-2) (H-2))
    fine<-cell (W-2) (H-2)
//the function that create the end of the path in the most difficult position
let findEnd()=
    let mutable possible=[]
    let mutable n=false
    let mutable way=0
    let mutable visited_Cell = []
    let mutable (a,b,wall) = cell 1 1
    let rec aux visited =
        match visited with
        |[]->visited // [] -> []
        |t::ts->let (x,y,w2) = t
                let mutable neighbours=[]
                let mutable direction=""
                if((isWall x (y+1))=false && not(List.contains (cell x (y+1)) visited_Cell)) then neighbours<-"d"::neighbours
                if((isWall x (y-1))=false && not(List.contains (cell x (y-1)) visited_Cell)) then neighbours<-"u"::neighbours 
                if((isWall (x-1) y)=false && not(List.contains (cell (x-1) y) visited_Cell)) then neighbours<-"l"::neighbours 
                if((isWall (x+1) y)=false && not(List.contains (cell (x+1) y) visited_Cell)) then neighbours<-"r"::neighbours
                if(neighbours.Length<>0)
                then  match (rnd_int 0 (neighbours.Length-1)) with
                             |0->direction<-neighbours.[0]
                     
                             |1->direction<-neighbours.[1]
                              
                             |2->direction<-neighbours.[2]


                             |3->direction<-neighbours.[3]

                             |_->direction<-""

                if((List.contains (x,y,w2) visited_Cell)=false) then visited_Cell <- [(x,y,w2)]@visited_Cell
                else ignore()

                match direction with
                        |"d"->n<-false
                              way<-way+1
                              aux ((cell x (y+1))::(x,y,w2)::ts)
                        |"u"->n<-false
                              way<-way+1
                              aux((cell x (y-1))::(x,y,w2)::ts)
                        |"l"->n<-false
                              way<-way+1
                              aux((cell (x-1) y)::(x,y,w2)::ts)
                        |"r"->n<-false
                              way<-way+1
                              aux ((cell (x+1) y)::(x,y,w2)::ts)
                        |_->if(n=false)
                            then possible<-(way,(cell x y))::possible
                            n<-true
                            way<-way-1
                            aux ts

    in aux ((a,b,wall)::[]) |>ignore
    //the function that find the position of the most distant end
    let rec best l c= let(ww,(a,b,d)) = c
                      match l with
                      |[]-> (a,b,d)
                      |x::xs-> let (ww2,(a2,b2,d2))=x
                               if (ww2>ww)
                               then best xs x
                               else best xs c
    in fine<-(best possible (0,cell (W-2) (H-2)))
//the function that search the solution of the maze based on the position passed
let solution px py=
    let mutable visited_Cell = []
    let (xf,yf,wf)=fine
    let rec aux visited =
        match visited with
        |[]->visited
        |t::ts->let (x,y,w2) = t
                if(x=xf && y=yf) then visited
                else let mutable neighbours=[]
                     let mutable direction=""
                     if((isWall x (y+1))=false && not(List.contains (cell x (y+1)) visited_Cell)) then neighbours<-"d"::neighbours
                     if((isWall x (y-1))=false && not(List.contains (cell x (y-1)) visited_Cell)) then neighbours<-"u"::neighbours 
                     if((isWall (x-1) y)=false && not(List.contains (cell (x-1) y) visited_Cell)) then neighbours<-"l"::neighbours 
                     if((isWall (x+1) y)=false && not(List.contains (cell (x+1) y) visited_Cell)) then neighbours<-"r"::neighbours
                     if(neighbours.Length<>0)
                     then  match (rnd_int 0 (neighbours.Length-1)) with
                             |0->direction<-neighbours.[0]
                     
                             |1->direction<-neighbours.[1]
                              
                             |2->direction<-neighbours.[2]


                             |3->direction<-neighbours.[3]

                             |_->direction<-""

                     if((List.contains (x,y,w2) visited_Cell)=false) then visited_Cell <- [(x,y,w2)]@visited_Cell
                     else ignore()

                     match direction with
                        |"d"->aux ((cell x (y+1))::(x,y,w2)::ts)
                        |"u"->aux((cell x (y-1))::(x,y,w2)::ts)
                        |"l"->aux((cell (x-1) y)::(x,y,w2)::ts)
                        |"r"->aux ((cell (x+1) y)::(x,y,w2)::ts)
                        |_->aux ts

    in aux ((px,py,false)::[])
//the list that contains the value of each cell
let mutable maze_String = []
//the list that contains the characters to make the titles
let mutable word_List = []

//temporary variable
let mutable temp = 0
//temporary variable
let mutable temp2 = 0

//One of the stats of the menù
let mutable win = false
//One of the stats of the menù
let mutable enter_Menu = true
//One of the stats of the menù
let mutable in_menu = false
//One of the stats of the menù
let mutable game_over = false
//One of the stats of the menù
let mutable random_mode = false
//One of the stats of the menù
let mutable normal_mode = false
//One of the stats of the menù
let mutable option = false
//the title that contains "YOU WIN"
let string_Win = "||  || |||  || ||  ||        || || |||    ||\n |||| || || || ||   ||      ||  || || |   ||\n  ||  || || || ||    || || ||   || ||  |  ||\n  ||  || || || ||     ||  ||    || ||   | ||\n  ||   |||   |||       |  |     || ||    |||\n"
//the title that contains "GAME OVER"
let string_Lose = " ||||    |||   |||| ||||  |||||     |||  ||     ||  |||||  ||||\n||      || ||  || ||| ||  ||       || ||  ||   ||   ||     || ||\n|| |||  ||_||  ||  |  ||  ||||     || ||   || ||    ||||   ||||\n||  ||  || ||  ||     ||  ||       || ||    |||     ||     || ||\n ||||   || ||  ||     ||  |||||     |||      |      |||||  || ||\n"
//the title that contains "MAZE" and "PLAY MODE"
let menu_String ="||||||||  ||||||||     ||||||       ||||||||||   |||||||||||\n||||||||||||||||||   ||||  ||||     ||||||||||   |||||||||||\n||||| |||||| |||||  ||||    ||||         ////    ||||\n|||||  ||||  |||||  ||||    ||||        ////     ||||||||||\n|||||   ||   |||||  ||||____||||       ////      ||||||||||\n|||||        |||||  ||||____||||      ////       ||||\n|||||        |||||  ||||    ||||     |||||||||   ||||||||||||\n|||||        |||||  ||||    ||||     |||||||||   ||||||||||||\n\n\n\n\n\n   ||||  ||    |||  ||  ||  |||| ||||  ||||  ||||  ||||||\n   ||  | ||   || ||  ||||   || ||| || ||  || || || ||\n   ||||  ||   ||_||   ||    || ||| || ||  || || || |||||\n   ||    ||   || ||   ||    ||  |  || ||  || || || ||\n   ||    |||| || ||   ||    ||     ||  ||||  ||||  ||||||\n  "
//the title that contains "CONTROLS"
let control_String =" |||  |||  |||    || |||||| ||||    |||  ||   |||||\n||   || || || |   ||   ||   || ||  || || ||   ||\n||   || || ||  |  ||   ||   ||||   || || ||   |||||\n||   || || ||   | ||   ||   || ||  || || ||      ||\n |||  |||  ||    |||   ||   || ||   |||  |||| |||||\n"
//the menù in the page CONTROLS
let controls_String ="\n\n KEY W : UP\n KEY A : LEFT\n KEY S : DOWN\n KEY D : RIGHT\n KEY E : FIND THE SOLUTION OF THE MAZE,AND RETURN TO THE MENU\n         IF YOU PRESS IT TWICE\n" 
//the menù in the main page
let play_String = "\n RANDOM\n\n NORMAL\n\n CONTROLS\n\n EXIT"

type state = {
    player : sprite
}
//the state that allows to show the solution of the maze
let mutable show=false
//the first call to create the first maze
build()
path()

//the list that contains the solution of the maze
let mutable solu = []

//the function that swaps the maze into a list of character
let swap_to_string() =
    for i in maze do
        let (e,f,w)=i
        if(w) 
             then if(f=W) 
                  then  maze_String <-maze_String@[CharInfo.wall]
                        temp <- 0
                        temp2 <- temp2+1
                   else maze_String<-maze_String@[CharInfo.wall]
             else if (f=W)
                  then maze_String<-maze_String@[CharInfo.path]
                       temp <- 0
                       temp2 <- temp2+1
                  else maze_String<-maze_String@[CharInfo.path]
        temp<-temp+1

//the function that swaps a string into the corresponding list of strings
let normal_swap_to_string (list:String) =
   let mutable temp_list = []
   for i=0 to list.Length-1 do
     if(list.[i] = ' ') then temp_list<-temp_list@[" "]
     if(list.[i] = '\n') then temp_list<-temp_list@["\n"]
     if(list.[i] = '|' || list.[i] = '_' || list.[i] = '/') then temp_list<-temp_list@["\219"]
   temp_list

//the main of the program             
let main()=
    let engine = new engine (W*2, H)

    //the first call of the function that creates the maze 
    swap_to_string()
    //the first call of the function that creates the menù
    word_List<-normal_swap_to_string(menu_String)

    let my_update (keyo : ConsoleKeyInfo option) (screen : wronly_raster) (st : state) =
        //the main structure "if" that changes function calls based on states 
        if(win) then build()
                     path()
                     maze_String<-[]
                     enter_Menu<-true
                     swap_to_string()
                     st.player.unsafe_plot(1,0,pixel.filled Color.DarkCyan)
                     st.player.unsafe_plot(0,0,pixel.filled Color.DarkCyan)
                     System.Console.ReadKey() |> ignore

        else if(option) then  word_List<-normal_swap_to_string(menu_String)
                              st.player.unsafe_plot(1,0,pixel.filled Color.DarkCyan)
                              st.player.unsafe_plot(0,0,pixel.filled Color.DarkCyan)
                              option<-false
                              enter_Menu<-true
                              System.Console.ReadKey() |> ignore
        //set the state win to false                   
        win<-false

        match keyo with
        | None -> ignore()
        | Some key ->
            // move player    
                    
                    
                    let dx, dy =
                        //the structure "if" that changes the movements based if it's shows the menù or the maze
                        if(in_menu)
                        then    match key.KeyChar with 
                                | 'w' -> if(in_menu && ((int st.player.y-1)>=((H/2)+1)&&(int st.player.y)<=((H/2)+7))) then 0.,-2.
                                         else 0.,0.
                                | 's' -> if(in_menu && ((int st.player.y)>=((H/2)+1)&&(int st.player.y+1)<=((H/2)+7))) then 0.,2.
                                         else 0.,0.
                                | '\r'-> if((int st.player.y)=((H/2)+1) && (int st.player.x)=(W-1))  then   random_mode<-true
                                                                                                            in_menu<-false
                                                                                                            st.player.x<-2.0
                                                                                                            st.player.y<-1.0
                                                                                                            st.player.unsafe_plot(1,0,pixel.filled Color.DarkCyan)
                                                                                                            st.player.unsafe_plot(0,0,pixel.filled Color.DarkCyan)
                                                                                                            0.,0.
                                         else if((int st.player.y)=((H/2)+3) && (int st.player.x)=(W-1))  then  normal_mode<-true
                                                                                                                in_menu<-false
                                                                                                                st.player.x<-2.0
                                                                                                                st.player.y<-1.0
                                                                                                                st.player.unsafe_plot(1,0,pixel.filled Color.DarkCyan)
                                                                                                                st.player.unsafe_plot(0,0,pixel.filled Color.DarkCyan)
                                                                                                                0.,0.
                                         else if((int st.player.y)=((H/2)+7) && (int st.player.x)=(W-1)) then  Environment.Exit(0)
                                                                                                               0.,0.
                                         else if((int st.player.y)=((H/2)+5) && (int st.player.x)=(W-1)) then option<-true 
                                                                                                              in_menu<-false
                                                                                                              0.,0.
                                                        
                                         else 0.,0.
                        
                                | _ -> 0., 0.

                        else    match key.KeyChar with 
                                | 'w' ->if(isWall ((int st.player.x)/2)  ((int st.player.y)-1) ) then 0.,0.
                                        else if(show) then 0.,0.  
                                        else 0.,-1.
                                | 's' ->if(isWall ((int st.player.x)/2)  ((int st.player.y)+1) ) then 0.,0.
                                        else if(show) then 0.,0. 
                                        else 0.,1.
                                | 'a' ->if(isWall (((int st.player.x)/2)-1)  (int st.player.y) ) then 0.,0.
                                        else if(show) then 0.,0. 
                                        else -2.0,0.
                                | 'd' ->if(isWall (((int st.player.x)/2)+1)  (int st.player.y) ) then 0.,0.
                                        else if(show) then 0.,0. 
                                        else 2.0,0.
                                | 'e' ->    if (show)
                                            then game_over<-true
                                                 0.,0.
                                            else solu <- solution ((int st.player.x)/2) (int st.player.y)
                                                 show<-true
                                                 0.,0.
                                | _ -> 0., 0.

                    st.player.move_by (dx, dy)

                    let (px,py,wz)=fine
                    //the structure "if" that checks if the player has won
                    if((((int st.player.x)/2) = px)&&(int st.player.y = py)) then win<-true
        let (px,py,wz)=fine
        //the structure "if" that changes the end of the maze based on the chosen mode
        if(random_mode) then findEnd()
                             random_mode<-false
        else if(normal_mode) then staticEnd()
                                  normal_mode<-false
 
        //the structure "if" that creates the screens to display based on the states
        if(win) then    word_List<-[]
                        word_List<-normal_swap_to_string(string_Win)
                        temp<-W/2
                        temp2<-H/2
                        for i=0 to word_List.Length-1 do
                            if(string_Win.[i]='\n') then temp2<-temp2+1
                                                         temp<-W/2
                            else screen.draw_text(word_List.[i],temp,temp2,Color.Yellow) 
                                 temp<-temp+1
                        screen.draw_text (sprintf "Press any key to return into the menu. ", 0, screen.height - 2, Color.White, Color.DarkMagenta)
                        st.player.x<-2.0
                        st.player.y<-1.0
                        st.player.clear
                        
        else if(game_over) then     win<-true
                                    game_over<-false
                                    show<-false
                                    word_List<-[]
                                    word_List<-normal_swap_to_string(string_Lose)
                                    temp<-W/3
                                    temp2<-H/2
                                    for i=0 to word_List.Length-1 do
                                        if(string_Lose.[i]='\n') then temp2<-temp2+1
                                                                      temp<-W/3
                                        else screen.draw_text(word_List.[i],temp,temp2,Color.Red) 
                                             temp<-temp+1
                                    screen.draw_text (sprintf "Press any key to return into the menu. ", 0, screen.height - 2, Color.White, Color.DarkMagenta)
                                    st.player.x<-2.0
                                    st.player.y<-1.0
                                    st.player.clear

        else if(enter_Menu) then    enter_Menu<-false  
                                    in_menu<-true
                                    st.player.x<-(float W-1.)
                                    st.player.y<-(float H/2. + 1.)
                                    st.player.unsafe_plot(1,0,CharInfo.menu)
                                    st.player.unsafe_plot(0,0,CharInfo.menu)
                          
        else if(in_menu) then   word_List<-normal_swap_to_string(menu_String)
                                temp<-W/2
                                temp2<-5
                                for i=0 to word_List.Length-1 do
                                    if(menu_String.[i]='\n') then temp2<-temp2+1
                                                                  temp<-W/2
                                    else screen.draw_text(word_List.[i],temp,temp2,Color.DarkGreen) 
                                         temp<-temp+1
                                screen.draw_text(play_String,W,H/2,Color.Green)

        else if(option) then    word_List<-normal_swap_to_string(control_String)
                                temp<-W/2
                                temp2<-5
                                for i=0 to word_List.Length-1 do
                                    if(control_String.[i]='\n') then temp2<-temp2+1
                                                                     temp<-W/2
                                    else screen.draw_text(word_List.[i],temp,temp2,Color.DarkGreen) 
                                         temp<-temp+1
                                screen.draw_text(controls_String,W/2,H/4,Color.Green)

                                screen.draw_text (sprintf "Press any key to return into the menu. ", 0, screen.height - 2, Color.White, Color.DarkMagenta)
                                st.player.x<-2.0
                                st.player.y<-1.0
                                st.player.clear
                               
        else                              
               for i=0 to maze.Length - 1 do
               let (a,b,w) = maze.[i]
               in if((a*2)=(px*2) && b=py) then screen.draw_line((a*2),b,((a*2)+1),b,CharInfo.finish)
                  else if (show=true && (List.contains maze.[i] solu)=true) 
                       then screen.draw_line((a*2),b,((a*2)+1),b,CharInfo.solution)
                       else screen.draw_line((a*2),b,((a*2)+1),b,maze_String.[i])


        
        
        {
        player = st.player
        }, match keyo with None -> false | Some k -> k.KeyChar = 'q'
   
    // create player sprite
    let player = engine.create_and_register_sprite (image (2, 1, pixel.filled Color.DarkCyan), 2, 1, 1)

    // initialize state
    let st0 = { 
        player = player
        }
    // start engine
    engine.loop my_update st0