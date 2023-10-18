	function deposit(
		address asset,
		uint256 amount,
		address onBehalfOf,
		uint16 referralCode
	) public override whenNotPaused {
		DataTypes.ReserveData storage reserve = _reserves[asset];

		ValidationLogic.validateDeposit(reserve, amount);

		address aToken = reserve.aTokenAddress;

		reserve.updateState();
		reserve.updateInterestRates(asset, aToken, amount, 0);

		IERC20(asset).safeTransferFrom(msg.sender, aToken, amount);

		if (IAToken(aToken).balanceOf(onBehalfOf) == 0) {
			_usersConfig[onBehalfOf].setUsingAsCollateral(reserve.id, true);
			emit ReserveUsedAsCollateralEnabled(asset, onBehalfOf);
		}

		IAToken(aToken).mint(onBehalfOf, amount, reserve.liquidityIndex);

		emit Deposit(asset, msg.sender, onBehalfOf, amount, referralCode);
	}