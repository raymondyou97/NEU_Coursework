import { async, ComponentFixture, TestBed } from '@angular/core/testing';

import { DAppConfiguratorComponent } from './d-app-configurator.component';

describe('DAppConfiguratorComponent', () => {
	let component: DAppConfiguratorComponent;
	let fixture: ComponentFixture<DAppConfiguratorComponent>;

	beforeEach(async(() => {
		TestBed.configureTestingModule({
			declarations: [DAppConfiguratorComponent]
		})
			.compileComponents();
	}));

	beforeEach(() => {
		fixture = TestBed.createComponent(DAppConfiguratorComponent);
		component = fixture.componentInstance;
		fixture.detectChanges();
	});

	it('should create', () => {
		expect(component).toBeTruthy();
	});
});
