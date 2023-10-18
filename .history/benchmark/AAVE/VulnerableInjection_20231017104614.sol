    function deposit(address _reserve, uint256 _amount, uint16 _referralCode)
        external
        payable
        nonReentrant
        onlyAmountGreaterThanZero(_amount)
    {
        AToken aToken = AToken(_reserve);

        bool isFirstDeposit = aToken.balanceOf(msg.sender) == 0;

        core.updateStateOnDeposit(_reserve, msg.sender, _amount, isFirstDeposit);

        //minting AToken to user 1:1 with the specific exchange rate
        aToken.mintOnDeposit(msg.sender, _amount);

        //transfer to the core contract
        core.transferToReserve.value(msg.value)(_reserve, msg.sender, _amount);

        //solium-disable-next-line
        emit Deposit(_reserve, msg.sender, _amount, _referralCode, block.timestamp);

    }