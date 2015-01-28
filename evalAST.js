F.evalAST = function(ast) {
  var env = [null,null,null];
  return ev(env,ast)[1];
};

function ev(env, ast) {
  if (typeof ast === "number" || typeof ast === "boolean" || typeof ast === "string" || ast === null) {
    return [env,ast];
  } else {
    var tag = ast[0];
    switch (tag) {
        case "+":
          var a1 = ev(env,ast[1])[1];
          var a2 = ev(env,ast[2])[1];
          checkArgs(a1,a2,"number");
          return [env, a1 + a2];
        case "-":
          var a1 = ev(env,ast[1])[1];
          var a2 = ev(env,ast[2])[1];
          checkArgs(a1,a2,"number");
          return [env, a1 - a2];
        case "*":          
          var a1 = ev(env,ast[1])[1];
          var a2 = ev(env,ast[2])[1];
          checkArgs(a1,a2,"number");
          return [env, a1 * a2];
        case "/":
          var a1 = ev(env,ast[1])[1];
          var a2 = ev(env,ast[2])[1];
          checkArgs(a1,a2,"number");        
          return [env, a1 / a2];
        case "%":
          var a1 = ev(env,ast[1])[1];
          var a2 = ev(env,ast[2])[1];
          checkArgs(a1,a2,"number");        
          return [env, a1 % a2];
        case "=":
          return [env, ev(env,ast[1])[1] === ev(env,ast[2])[1]];
        case "!=":
          return [env, ev(env,ast[1])[1] !== ev(env,ast[2])[1]];
        case "<":
          var a1 = ev(env,ast[1])[1];
          var a2 = ev(env,ast[2])[1];
          checkArgs(a1,a2,"number");        
          return [env, a1 < a2];
        case ">":
          var a1 = ev(env,ast[1])[1];
          var a2 = ev(env,ast[2])[1];
          checkArgs(a1,a2,"number");        
          return [env, a1 > a2];
        case "and":
          var a1 = ev(env,ast[1])[1];
          var a2 = ev(env,ast[2])[1];
          checkArgs(a1,a2,"boolean");          
          return [env, a1 && a2];
        case "or":
          var a1 = ev(env,ast[1])[1];
          var a2 = ev(env,ast[2])[1];
          checkArgs(a1,a2,"boolean");        
          return [env, a1 || a2];
        case "if":
          var cond = ev(env,ast[1])[1];
          if(typeof cond !== "boolean"){
            throw new Error("if requires boolean");
          }
          return [env, cond ? ev(env,ast[2])[1] : ev(env,ast[3])[1]];
        case "id":
          var c_env=env;
          while(c_env[2]!==null){
            if(c_env[0]===ast[1]){
              return [env, c_env[1]]; 
            }
            c_env=c_env[2];
          }
          throw new Error("undeclared id:"+ast[1]);
        case "let":
          var id=ev(env,ast[1])[1];
          var val=ev(env,ast[2])[1];
          val=updateClosures(id,val,val);
          var newenv = [id,val,env];
          //val=ev(newenv,ast[2]);
          //newenv = [id,val,env];
          return ev(newenv,ast[3]);
        case "fun":
          var args=ast[1];
          var body=ast[2];
          return [env,["closure",args,body,env]];
        case "call":
          var f=ev(env,ast[1])[1];
          var index=-1;
          var newenv;
          var val;
          var id;
          if(f[0]!=="closure"){
            throw new Error("call on non-function type");
          }
          var args = ast.slice(2);
          /*if(f[1].length<args.length){
            throw new Error("wrong number of arguments");
          }*/

          //curry time
          if(args.length<f[1].length){
            for(var i=0;i<args.length;i++){
              for(index++;index<f[1].length;index++){
                if(!isPrim(f[1][index])) break;
              }
              val=ev(env,args[i])[1];
              id=f[1][index];
              f[1][index]=val;
              f[3]=[id,val,f[3]];
            }
            if(index<f[1].length-1){
              return [env,f];
            }
          }

          //make env = arguments env -> closure env
          newenv=f[3];
          var aval;
          for(var i=0;i<args.length;i++){
            if(typeof args[i] === "number" || typeof args[i] === "boolean"){
              aval=args[i];
            } else {
              aval=ev(env,args[i])[1];
            }
            newenv=[f[1][i],aval,newenv];
          }
          var c_env=env;
          while(c_env[2]!==null){
            if(c_env[1]===f){
              newenv=[c_env[0],c_env[1],newenv];
            }
            c_env=c_env[2];
          }
          return [env, ev(newenv,f[2])[1]];
        case "cons":
          return [env,["cons",ev(env,ast[1])[1],ev(env,ast[2])[1]]];
        case "seq":
          newenv=ev(env,ast[1])[0];
          return ev(newenv,ast[2]);
        case "match":
          var p=ev(env,ast[1])[1];
          var patterns = ast.slice(2);
          for(var i=0;i<patterns.length;i+=2){
            var newenv = matchRec(env,p,patterns[i]);
            if(newenv==="no") continue;
            return ev(newenv,patterns[i+1]);
          }
          throw new Error("match failure");
        case "set":
          var c_env=env;
          var head=c_env;
          while(c_env[2]!==null){
            if(c_env[0]===ast[1]){
              var val=ev(env,ast[2])[1];
              c_env[1]=val;
              return [head,val];
            }
            c_env=c_env[2];
          }
          throw new Error("set on undeclared id:"+ast[1]);
        case "listComp":
          var expr=ast[1];
          var id=ast[2];
          var list=ev(env,ast[3])[1];
          var outList;
          var head=null;
          var newenv;
          var val;
          var pred;
          if(ast.length===5){
            pred=ast[4];
          }
          while(list!==null){
            newenv=[id,list[1],env];
            if(ast.length===5){
              if(!ev(newenv,pred)[1]){
                list=list[2];
                continue;
              }
            }
            val=["cons",ev(newenv,expr)[1],null];
            if(outList===undefined){
              outList=val;
              head=outList;
            }else{
              outList[2]=val;
              outList=outList[2];
            }
            list=list[2];
          }
          return [env,head];
        case "delay":
          //var e=ev(env,ast[1])[1];
          var newenv=[];
          return [env,["closure",[],ast[1],env]];
        case "force":
          //var e=ev(env,ast[1])[1];
          //console.log(env[1][2][1]="rest");
          return [env,ev(env,["call",ast[1]])[1]];
           
    }
  }
}

function checkArgs(ast1,ast2,type){
  if(typeof ast1 !== type || typeof ast2 !== type){
    throw new Error("incorrect type to operator");
  }
  return;
}

function isPrim(t){
  if(typeof t === "boolean" || typeof t === "number"){
    return true;
  } else return false;
}

function matchRec(env,matchExpr,pattern){
  if(pattern===null){
    if(matchExpr!==null){
      return "no";
    } else {
      return env;
    }
  } else if(typeof pattern === "number" || typeof pattern === "boolean"){
    if(matchExpr===pattern){
      return env;
    } else {
      return "no";
    }
  } else if(pattern[0]==="_"){
    return env;
    if(matchExpr ===null || typeof matchExpr ==="number" || typeof matchExpr ==="boolean"){
      return env;
    } else if(matchExpr[0]==="cons"){
      return env;
    } else {
      return "no";
    }
  } else if(pattern[0]==="id") {
    return [pattern[1], matchExpr, env];
    /*
    if(matchExpr === null){
      return [pattern[1], matchExpr, env];
    } else if(typeof matchExpr ==="number" || typeof matchExpr ==="boolean"){
      return [pattern[1], matchExpr, env];
    } else if(matchExpr[0]==="cons" || matchExpr[0]==="closure"){
      return [pattern[1], matchExpr, env];
    } else {
      return "no";
    }*/
  } else if(pattern[0]==="cons"){
    if(matchExpr===null){
      return "no";
    }
    if(matchExpr[0]!=="cons"){
      return "no";
    } else {
      var r1,r2;
      r1=matchRec(env,matchExpr[1],pattern[1]);
      if(r1==="no"){
        return "no";
      }
      r2=matchRec(r1,matchExpr[2],pattern[2]);
      return r2;
    }
  }
}

function updateClosures(id,topVal,val){
  console.log(val);
  if(val===null || typeof val === "number" || typeof val === "boolean"){
    return val;
  }

  if(val[0]==="cons"){
    val[1]=updateClosures(id,topVal,val[1]);
    val[2]=updateClosures(id,topVal,val[2]);
    return val;
  }

  if(val[0]==="closure"){
    val[3]=[id,topVal,val[3]];
    return val;
  }
}
/* obsolete??? complete waste of time?
function replaceRecur(env,id,val){
  if(typeof val === "number" || typeof val === "boolean" || typeof val === "string" || val === null){
    return [env,val];
  }

  switch(val[1]){
    case "+":
    case "-":
    case "*":          
    case "/":
    case "%":
    case "=":
    case "!=":
    case "<":
    case ">":
    case "and":
    case "or":
    case "id":
      return [env, val];
    case "if":
      var val[1]=replaceRecur(env,val[1])[1];
      var val[2]=replaceRecur(env,val[2])[1];
      var val[3]=replaceRecur(env,val[3])[1];
      return [env,val];
      if(val[1]===id){
        val[1]=newid;
      }
      return val;
    case "let":
      if(val[1]===id){
        return [env,val];
      }
      var val[2]=replaceRecur(val[2]);
      return [env,val];
    case "fun":
      var args=val[1];
      for(var i;i<args.length;i++){
        if(args[i]===id){
          return [env,val];
        }
      }
      var val[2]=replaceRecur(val[2]);
      return [env,val];
    case "call":
      //NOT SURE SO IGNORED
      return [env,val];
      /**
      //if id in argNames break, if id in args passed...need to replace in that function
      var f=val[1];
      var args = val.slice(2);
      for(var i=0;i<args.length;i++){
        if(args[i]===id){
          args[i]=newid;
          f=replaceRecur(val[1]);
        }
      }

      var index=-1;
      var newenv;
      var val;
      var id;
      if(f[0]!=="closure"){
        throw new Error("call on non-function type");
      }
      var args = ast.slice(2);

      //curry time
      if(args.length<f[1].length){
        for(var i=0;i<args.length;i++){
          for(index++;index<f[1].length;index++){
            if(!isPrim(f[1][index])) break;
          }
          val=ev(env,args[i])[1];
          id=f[1][index];
          f[1][index]=val;
          f[3]=[id,val,f[3]];
        }
        if(index<f[1].length-1){
          return [env,f];
        }
      }

      //make env = arguments env -> closure env
      newenv=f[3];
      var aval;
      for(var i=0;i<args.length;i++){
        if(typeof args[i] === "number" || typeof args[i] === "boolean"){
          aval=args[i];
        } else {
          aval=ev(env,args[i])[1];
        }
        newenv=[f[1][i],aval,newenv];
      }
      var c_env=env;
      while(c_env[2]!==null){
        if(c_env[1]===f){
          newenv=[c_env[0],c_env[1],newenv];
          break;
        }
        c_env=c_env[2];
      }
      return [env, ev(newenv,f[2])[1]];
    case "cons":
      val[1]=replaceRecur(env,val[1])[1];
      val[2]=replaceRecur(env,val[2])[1];
      return [env,val];
    case "seq":
      var newenv=replaceRecur(env,val[1])[0];
      return replaceRecur(newenv,val[2]);
    case "match":
      var p=ev(env,ast[1])[1];
      var patterns = ast.slice(2);
      for(var i=0;i<patterns.length;i+=2){
        var newenv = matchRec(env,p,patterns[i]);
        if(newenv==="no") continue;
        return ev(newenv,patterns[i+1]);
      }
      throw new Error("match failure");
    case "set":
      var c_env=env;
      var head=c_env;
      while(c_env[2]!==null){
        if(c_env[0]===ast[1]){
          var val=ev(env,ast[2])[1];
          c_env[1]=val;
          return [head,val];
        }
        c_env=c_env[2];
      }
      throw new Error("set on undeclared id:"+ast[1]);
    case "listComp":
      var expr=ast[1];
      var id=ast[2];
      var list=ev(env,ast[3])[1];
      var outList;
      var head=null;
      var newenv;
      var val;
      var pred;
      if(ast.length===5){
        pred=ast[4];
      }
      while(list!==null){
        newenv=[id,list[1],env];
        if(ast.length===5){
          if(!ev(newenv,pred)[1]){
            list=list[2];
            continue;
          }
        }
        val=["cons",ev(newenv,expr)[1],null];
        if(outList===undefined){
          outList=val;
          head=outList;
        }else{
          outList[2]=val;
          outList=outList[2];
        }
        list=list[2];
      }
      return [env,head];
    case "delay":
      //var e=ev(env,ast[1])[1];
      return [env,["closure",[],ast[1],env]];
    case "force":
      //var e=ev(env,ast[1])[1];
      return [env,ev(env,["call",ast[1]])[1]];
  }
}*/
